#include <iostream>
#include <fstream>
#include <string>
#include <filesystem>
#include <stdexcept>
#include <map>
#include <vector>
#include <sstream>
#include <array>
#include <iomanip>
#include <cctype>
#include <stdexcept>
#include <mbedtls/aes.h>
#include <mbedtls/cipher.h>

// Namespace alias for filesystem
namespace fs = std::filesystem;

// ---------------- Partition struct ----------------
struct Partition {
    std::string name;
    uint64_t hfs0_offset;
    uint64_t rel_offset;
    uint64_t offset;
    uint64_t size;
};

struct FsEntry {
    uint32_t start;
    uint32_t end;
};

struct NcaHeader {
    char magic[4];
    uint8_t distribution_type;
    uint8_t content_type;
    uint8_t keygen_old;
    uint8_t key_area_key_index;
    uint64_t content_size;
    uint64_t program_id;
    uint32_t content_index;
    uint32_t sdk_addon_version;
    uint8_t keygen;
    uint8_t signature_keygen;
    std::array<uint8_t, 16> rights_id; // 0x10 bytes
    std::vector<uint8_t> key_area;     // 0x40 bytes
    std::vector<FsEntry> fs_entries;   // 4 entries
};

struct Region {
    uint64_t offset;
    uint64_t size;
};

struct HierarchicalSha256Data {
    std::array<uint8_t, 0x20> master_hash;
    uint32_t hash_block_size;
    uint32_t hash_layer_count;
    std::vector<Region> hash_layer_region;
};

struct IntegrityLevel {
    uint64_t offset;
    uint64_t size;
    uint32_t block_order;
};

struct IntegrityMetaInfo {
    uint32_t magic;
    uint32_t version;
    uint32_t master_hash_size;
    uint32_t max_layers;
    std::vector<IntegrityLevel> levels;
};

struct NcaPatchInfo {
    uint64_t indirect_offset = 0;
    uint64_t indirect_size = 0;
    std::array<uint8_t, 0x10> indirect_header{};

    uint64_t aes_ctr_ex_offset = 0;
    uint64_t aes_ctr_ex_size = 0;
    std::array<uint8_t, 0x10> aes_ctr_ex_header{};

    bool has_indirect_table() const {
        return indirect_size != 0;
    }

    bool has_aes_ctr_ex_table() const {
        return aes_ctr_ex_size != 0;
    }
};

struct NcaFsHeader{
    uint16_t version;
    uint8_t fs_type;
    uint8_t hash_type;
    uint8_t encryption_type;
    uint8_t metadata_hash_type;
    HierarchicalSha256Data sha256;
    IntegrityMetaInfo integrity;
    NcaPatchInfo patch_info;

    std::array<uint8_t, 4> Generation;
    std::array<uint8_t, 4> SecureValue;

    // Dummy hash region size
    uint64_t hash_region_size() const {
        // Hierarchical SHA256 (PartitionFS)
        if (hash_type == 2 || hash_type == 5)
        {
            if (sha256.hash_layer_count == 0)
                throw std::runtime_error("Invalid SHA256 layer count");

            return sha256.hash_layer_region[sha256.hash_layer_count - 1].offset;
        }

        // Integrity hash (RomFS)
        if (hash_type == 3 || hash_type == 6)
        {
            if (integrity.max_layers < 2)
                throw std::runtime_error("Invalid integrity layer count");

            return integrity.levels[integrity.max_layers - 2].offset;
        }

        throw std::runtime_error("Unsupported hash_type");
    }
};

// Define CHUNK_SIZE as 1MB (0x100000 bytes)
const size_t CHUNK_SIZE = 0x100000;

static constexpr std::size_t SectorShift = 9; 
static constexpr uint64_t SectorToByte(uint32_t sector) { return static_cast<uint64_t>(sector) << SectorShift; }

std::vector<uint8_t> hex_to_bytes(const std::string& hex) {
    if (hex.size() % 2 != 0) {
        throw std::runtime_error("Invalid hex string length");
    }

    std::vector<uint8_t> bytes;
    for (size_t i = 0; i < hex.size(); i += 2) {
        uint8_t byte = (uint8_t)std::stoi(hex.substr(i, 2), nullptr, 16);
        bytes.push_back(byte);
    }
    return bytes;
}

// Helper function to read little-endian uint32_t
uint32_t read_u32_le(const uint8_t * buf) {
    return static_cast<uint32_t>(
        (uint8_t)buf[0] |
        ((uint8_t)buf[1] << 8) |
        ((uint8_t)buf[2] << 16) |
        ((uint8_t)buf[3] << 24)
        );
}

uint32_t read_u32_be(const uint8_t* p)
{
    return (uint32_t(p[0]) << 24) |
        (uint32_t(p[1]) << 16) |
        (uint32_t(p[2]) << 8) |
        (uint32_t(p[3]));
}

uint64_t read_u64_le(const uint8_t * buf) {
    return static_cast<uint64_t>(
        (uint64_t)buf[0] |
        ((uint64_t)buf[1] << 8) |
        ((uint64_t)buf[2] << 16) |
        ((uint64_t)buf[3] << 24) |
        ((uint64_t)buf[4] << 32) |
        ((uint64_t)buf[5] << 40) |
        ((uint64_t)buf[6] << 48) |
        ((uint64_t)buf[7] << 56)
        );
}

void write_u64_be(uint8_t* p, uint64_t v)
{
    p[0] = (v >> 56) & 0xFF;
    p[1] = (v >> 48) & 0xFF;
    p[2] = (v >> 40) & 0xFF;
    p[3] = (v >> 32) & 0xFF;
    p[4] = (v >> 24) & 0xFF;
    p[5] = (v >> 16) & 0xFF;
    p[6] = (v >> 8) & 0xFF;
    p[7] = (v) & 0xFF;
}

NcaHeader parse_nca_header(const std::vector<uint8_t>& buf) {
    NcaHeader hdr;

    // Copy magic
    std::memcpy(hdr.magic, buf.data() + 0x200, 4);

    hdr.distribution_type = static_cast<uint8_t>(buf[0x204]);
    hdr.content_type = static_cast<uint8_t>(buf[0x205]);
    hdr.keygen_old = static_cast<uint8_t>(buf[0x206]);
    hdr.key_area_key_index = static_cast<uint8_t>(buf[0x207]);
    hdr.content_size = read_u64_le(buf.data() + 0x208);
    hdr.program_id = read_u64_le(buf.data() + 0x210);
    hdr.content_index = read_u32_le(buf.data() + 0x218);
    hdr.sdk_addon_version = read_u32_le(buf.data() + 0x21C);
    hdr.keygen = static_cast<uint8_t>(buf[0x220]);
    hdr.signature_keygen = static_cast<uint8_t>(buf[0x221]);

    // Copy rights_id (16 bytes)
    std::memcpy(hdr.rights_id.data(), buf.data() + 0x230, 16);

    // Copy key_area (0x40 bytes)
    hdr.key_area.assign(buf.begin() + 0x300, buf.begin() + 0x340);

    // Parse FS entries (4 entries, each 0x10 bytes)
    hdr.fs_entries.resize(4);
    for (int i = 0; i < 4; ++i) {
        const uint8_t * fs = buf.data() + 0x240 + i * 0x10;
        hdr.fs_entries[i].start = read_u32_le(fs);
        hdr.fs_entries[i].end = read_u32_le(fs + 4);
    }

    return hdr;
}

HierarchicalSha256Data parse_hierarchical_sha256(const std::vector<uint8_t>& buf)
{
    if (buf.size() < 0x28)
        throw std::runtime_error("SHA256 header too small");

    HierarchicalSha256Data out{};

    // master_hash
    std::copy(buf.begin(), buf.begin() + 0x20, out.master_hash.begin());

    // hash_block_size
    out.hash_block_size = read_u32_le(&buf[0x20]);

    // hash_layer_count
    out.hash_layer_count = read_u32_le(&buf[0x24]);

    size_t base = 0x28;
    size_t needed = base + out.hash_layer_count * 0x10;

    if (buf.size() < needed)
        throw std::runtime_error("SHA256 region table truncated");

    out.hash_layer_region.reserve(out.hash_layer_count);

    for (uint32_t i = 0; i < out.hash_layer_count; i++)
    {
        size_t pos = base + i * 0x10;

        Region r;
        r.offset = read_u64_le(&buf[pos + 0x00]);
        r.size = read_u64_le(&buf[pos + 0x08]);

        out.hash_layer_region.push_back(r);
    }

    return out;
}

NcaPatchInfo parse_patch_info(const std::vector<uint8_t>& buf)
{
    NcaPatchInfo out{};
    out.indirect_offset = read_u64_le(&buf[0x00]);
    out.indirect_size = read_u64_le(&buf[0x08]);
    std::copy(buf.begin() + 0x10, buf.begin() + 0x20, out.indirect_header.begin());
    out.aes_ctr_ex_offset = read_u64_le(&buf[0x20]);
    out.aes_ctr_ex_size = read_u64_le(&buf[0x28]);
    std::copy(buf.begin() + 0x30, buf.begin() + 0x40, out.aes_ctr_ex_header.begin());
    return out;
}

IntegrityMetaInfo parse_integrity_meta(const std::vector<uint8_t>& buf)
{
    if (buf.size() < 0x10)
        throw std::runtime_error("Integrity meta too small");

    IntegrityMetaInfo out{};

    out.magic = read_u32_le(&buf[0x00]);
    out.version = read_u32_le(&buf[0x04]);
    out.master_hash_size = read_u32_le(&buf[0x08]);
    out.max_layers = read_u32_le(&buf[0x0C]);

    if (out.max_layers < 2)
        throw std::runtime_error("Integrity meta invalid layer count");

    size_t base = 0x10;
    size_t level_count = out.max_layers - 1;
    size_t needed = base + level_count * 0x18;

    if (buf.size() < needed)
        throw std::runtime_error("Integrity level table truncated");

    out.levels.reserve(level_count);

    for (size_t i = 0; i < level_count; ++i)
    {
        size_t pos = base + i * 0x18;

        IntegrityLevel lvl;
        lvl.offset = read_u64_le(&buf[pos + 0x00]);
        lvl.size = read_u64_le(&buf[pos + 0x08]);
        lvl.block_order = read_u32_le(&buf[pos + 0x10]);

        out.levels.push_back(lvl);
    }

    return out;
}

NcaFsHeader parse_nca_fs_header(const std::vector<char>& buf) {
    if (buf.size() != 0x200) throw std::runtime_error("FS header must be 0x200 bytes");

    NcaFsHeader hdr{ 0 };
    hdr.version = static_cast<uint16_t>((uint8_t)buf[0] | ((uint8_t)buf[1] << 8));
    hdr.fs_type = static_cast<uint8_t>(buf[2]);
    hdr.hash_type = static_cast<uint8_t>(buf[3]);
    hdr.encryption_type = static_cast<uint8_t>(buf[4]);
    hdr.metadata_hash_type = static_cast<uint8_t>(buf[5]);

    std::copy(buf.begin() + 0x140, buf.begin() + 0x144, hdr.Generation.begin());
    std::copy(buf.begin() + 0x144, buf.begin() + 0x148, hdr.SecureValue.begin());
    std::vector<uint8_t> hash_data(buf.begin() + 0x08, buf.begin() + 0x100);

    if (hdr.hash_type == 2 || hdr.hash_type == 5)
        hdr.sha256 = parse_hierarchical_sha256(hash_data);

    else if (hdr.hash_type == 3 || hdr.hash_type == 6)
        hdr.integrity = parse_integrity_meta(hash_data);

    std::vector<uint8_t> patch_data(buf.begin() + 0x100, buf.begin() + 0x140);
    hdr.patch_info = parse_patch_info(patch_data);
    return hdr;
}

class KeyStore {
public:
    std::map<int, std::vector<uint8_t>> titlekek;  // keygen -> 16-byte AES key
    std::map<std::string, std::vector<uint8_t>> keys;
    std::map<std::string, std::vector<uint8_t>> titlekeys;

    void set(const std::string& key, const std::vector<uint8_t>& value) {
        keys[key] = value;
    }

    std::vector<uint8_t> get(const std::string& key) const {
        auto it = keys.find(key);
        if (it != keys.end()) return it->second;
        throw std::runtime_error("Key not found: " + key);
    }
};

// Load keys from simple INI file
KeyStore load_keys(const std::string& key_file) {
    KeyStore ks;
    std::ifstream fin(key_file);
    if (!fin) {
        throw std::runtime_error("Cannot open key file: " + key_file);
    }

    std::string line;
    while (std::getline(fin, line)) {
        // Trim whitespace
        line.erase(0, line.find_first_not_of(" \t\r\n"));
        line.erase(line.find_last_not_of(" \t\r\n") + 1);

        if (line.empty() || line.find('=') == std::string::npos)
            continue;

        auto pos = line.find('=');
        std::string key = line.substr(0, pos);
        std::string value_str = line.substr(pos + 1);

        // Trim key/value
        key.erase(0, key.find_first_not_of(" \t\r\n"));
        key.erase(key.find_last_not_of(" \t\r\n") + 1);
        value_str.erase(0, value_str.find_first_not_of(" \t\r\n"));
        value_str.erase(value_str.find_last_not_of(" \t\r\n") + 1);

        std::vector<uint8_t> value = hex_to_bytes(value_str);

        // Handle titlekek separately
        if (key.find("titlekek") == 0) {
            std::string suffix = key.substr(8);
            suffix.erase(0, suffix.find_first_not_of("_"));
            if (!suffix.empty() && std::isxdigit(suffix[0]) && suffix.size() == 1) {
                int idx = std::stoi(suffix, nullptr, 16);
                ks.titlekek[idx] = value;
            }
            else {
                ks.set(key, value);  // fallback
            }
        }
        else {
            ks.set(key, value);
        }
    }

    return ks;
}

std::array<uint8_t, 16> nintendo_tweak(uint64_t sector) {
    std::array<uint8_t, 16> t{};
    for (int i = 0; i < 16; i++) {
        t[15 - i] = static_cast<uint8_t>(sector & 0xFF);
        sector >>= 8;
    }
    return t;
}

void gf_mul_x(std::array<uint8_t, 16>& v)
{
    uint8_t carry = 0;

    for (int i = 15; i >= 0; --i) {
        uint8_t new_carry = (v[i] >> 7) & 1;
        v[i] = (v[i] << 1) | carry;
        carry = new_carry;
    }

    if (carry)
        v[15] ^= 0x87;
}

void aes_ecb_decrypt_block(const std::array<uint8_t, 16>& key,
    const std::array<uint8_t, 16>& in,
    std::array<uint8_t, 16>& out)
{
    mbedtls_aes_context ctx;
    mbedtls_aes_init(&ctx);

    mbedtls_aes_setkey_dec(&ctx, key.data(), 128);
    mbedtls_aes_crypt_ecb(&ctx, MBEDTLS_AES_DECRYPT, in.data(), out.data());

    mbedtls_aes_free(&ctx);
}

void aes_ecb_encrypt_block(const std::array<uint8_t, 16>& key,
    const std::array<uint8_t, 16>& in,
    std::array<uint8_t, 16>& out)
{
    mbedtls_aes_context ctx;
    mbedtls_aes_init(&ctx);

    mbedtls_aes_setkey_enc(&ctx, key.data(), 128);
    mbedtls_aes_crypt_ecb(&ctx, MBEDTLS_AES_ENCRYPT, in.data(), out.data());

    mbedtls_aes_free(&ctx);
}

std::vector<uint8_t> aes_xts_decrypt(
    const std::vector<uint8_t>& data,
    const std::vector<uint8_t>& key,
    uint64_t base_sector = 0,
    size_t sector_size = 0x200
) {
    // Check that the key is 32 bytes (for AES-256-XTS)
    if (key.size() != 32) {
        throw std::runtime_error("Header key must be 32 bytes (256 bits)");
    }

    // Initialize the cipher context
    mbedtls_cipher_context_t ctx;
    mbedtls_cipher_init(&ctx);

    // Setup AES cipher for AES-128-XTS
    if (mbedtls_cipher_setup(&ctx, mbedtls_cipher_info_from_type(MBEDTLS_CIPHER_AES_128_XTS)) != 0) {
        throw std::runtime_error("Failed to set up AES-XTS cipher context");
    }

    // Set the key (first part of AES-XTS key)
    if (mbedtls_cipher_setkey(&ctx, key.data(), 256, MBEDTLS_DECRYPT) != 0) {
        throw std::runtime_error("Failed to set key1 for AES-XTS");
    }

    // Prepare output vector
    std::vector<uint8_t> out(data.size());
    size_t num_sectors = data.size() / sector_size;

    // Decrypt each sector
    for (size_t sector_index = 0; sector_index < num_sectors; ++sector_index) {
        size_t sector_offset = sector_index * sector_size;

        std::array<uint8_t, 16> tweak =
            nintendo_tweak(base_sector + sector_index);

        if (mbedtls_cipher_set_iv(&ctx, tweak.data(), 16) != 0)
            throw std::runtime_error("cipher_set_iv failed");

        if (mbedtls_cipher_reset(&ctx) != 0)
            throw std::runtime_error("cipher_reset failed");

        size_t block_size;
        if (mbedtls_cipher_update(&ctx, data.data() + sector_offset, sector_size, out.data() + sector_offset, &block_size) != 0) {
            throw std::runtime_error("Failed to decrypt AES-XTS block");
        }
        if (block_size != sector_size) {
            throw std::runtime_error("Failed to decrypt AES-XTS block");
        }
    }

    // Clean up the cipher context
    mbedtls_cipher_free(&ctx);

    return out;
}

std::vector<uint8_t> aes_128_ecb_decrypt(const std::vector<uint8_t>& key, const std::vector<uint8_t>& data) {
    mbedtls_aes_context aes_ctx;
    mbedtls_aes_init(&aes_ctx);

    // Set AES decryption key
    if (mbedtls_aes_setkey_dec(&aes_ctx, key.data(), 128) != 0) {
        throw std::runtime_error("AES key setup failed");
    }

    std::vector<uint8_t> decrypted_data(data.size());
    size_t offset = 0;

    // Decrypt in blocks of 16 bytes (AES block size)
    while (offset < data.size()) {
        if (mbedtls_aes_crypt_ecb(&aes_ctx, MBEDTLS_AES_DECRYPT, data.data() + offset, decrypted_data.data() + offset) != 0) {
            throw std::runtime_error("AES decryption failed");
        }
        offset += 16;
    }

    mbedtls_aes_free(&aes_ctx);
    return decrypted_data;
}

std::vector<uint8_t> aes_ctr_decrypt(const std::vector<uint8_t>& enc, const std::vector<uint8_t>& key,
    const NcaFsHeader& section, uint64_t section_offset) {
    size_t sector_size = 0x10; // 16 bytes per sector
    uint64_t sector_index = section_offset / sector_size;
    size_t sector_offset_within_block = section_offset % sector_size;
    size_t byte_offset = sector_offset_within_block % 16;

    std::vector<uint8_t> out;
    size_t pos = 0;

    mbedtls_aes_context aes;
    mbedtls_aes_init(&aes);

    while (pos < enc.size()) {
        // Construct the IV using the nintendo_tweak and section parameters
        std::array<uint8_t, 16> iv = nintendo_tweak(sector_index);
        std::copy(section.SecureValue.rbegin(), section.SecureValue.rend(), iv.begin());
        std::copy(section.Generation.rbegin(), section.Generation.rend(), iv.begin() + 4);

        uint8_t ks[16];
        mbedtls_aes_setkey_enc(&aes, key.data(), 128);  // AES-128 encryption
        mbedtls_aes_crypt_ecb(&aes, MBEDTLS_AES_ENCRYPT, iv.data(), ks);  // AES ECB encryption for the keystream

        size_t n = std::min(enc.size() - pos, 16 - byte_offset);
        for (size_t i = 0; i < n; ++i) {
            out.push_back(enc[pos + i] ^ ks[byte_offset + i]);
        }
        pos += n;
        byte_offset = 0;
        ++sector_index;
    }

    mbedtls_aes_free(&aes);
    return out;
}
int get_master_key_index(uint8_t keygen) {
    if (keygen <= 2) {
        return keygen;
    }
    return keygen - 1;
}

std::vector<uint8_t> get_key_area_key(const KeyStore& keys, const NcaHeader& nca_header) {
    int keygen = get_master_key_index(nca_header.keygen); // Get keygen index

    // Build the master key name
    std::ostringstream ss;
    ss << "master_key_"
        << std::hex << std::nouppercase
        << std::setw(2) << std::setfill('0')
        << keygen;
    ;
    std::string master_key_name = ss.str();
    if (keys.keys.find(master_key_name) == keys.keys.end()) {
        throw std::runtime_error("Missing " + master_key_name);
    }
    const std::vector<uint8_t>& master_key = keys.keys.at(master_key_name);

    // Determine the source name for the key area key based on key_area_key_index
    std::string src_name;
    switch (nca_header.key_area_key_index) {
    case 0:
        src_name = "key_area_key_application_source";
        break;
    case 1:
        src_name = "key_area_key_ocean_source";
        break;
    case 2:
        src_name = "key_area_key_system_source";
        break;
    default:
        throw std::runtime_error("Invalid key_area_key_index: " + std::to_string(nca_header.key_area_key_index));
    }

    if (keys.keys.find(src_name) == keys.keys.end()) {
        throw std::runtime_error("Missing " + src_name);
    }
    const std::vector<uint8_t>& key_area_src = keys.keys.at(src_name);

    if (keys.keys.find("aes_kek_generation_source") == keys.keys.end()) {
        throw std::runtime_error("Missing aes_kek_generation_source");
    }
    const std::vector<uint8_t>& aes_kek_src = keys.keys.at("aes_kek_generation_source");

    if (keys.keys.find("aes_key_generation_source") == keys.keys.end()) {
        throw std::runtime_error("Missing aes_key_generation_source");
    }
    const std::vector<uint8_t>& aes_keygen_src = keys.keys.at("aes_key_generation_source");

    // Decrypt using AES in ECB mode
    std::vector<uint8_t> kek = aes_128_ecb_decrypt(master_key, aes_kek_src);
    std::vector<uint8_t> keygen_key = aes_128_ecb_decrypt(kek, key_area_src);
    std::vector<uint8_t> key_area_key = aes_128_ecb_decrypt(keygen_key, aes_keygen_src);

    return key_area_key;
}

// Retrieve the Title KEK for a given NCA
std::vector<uint8_t> get_title_kek_key(const KeyStore& keys, const NcaHeader& nca_header) {
    int keygen = get_master_key_index(nca_header.keygen); // Get keygen index

    // Build the master key name
    std::ostringstream ss;
    ss << "master_key_"
        << std::hex << std::nouppercase
        << std::setw(2) << std::setfill('0')
        << keygen;
    ;
    std::string master_key_name = ss.str();
    if (keys.keys.find(master_key_name) == keys.keys.end()) {
        throw std::runtime_error("Missing " + master_key_name);
    }
    const std::vector<uint8_t>& master_key = keys.keys.at(master_key_name);

    if (keys.keys.find("titlekek_source") == keys.keys.end()) {
        throw std::runtime_error("Missing titlekek_source");
    }
    const std::vector<uint8_t>& title_kek_src = keys.keys.at("titlekek_source");
    std::vector<uint8_t> title_kek = aes_128_ecb_decrypt(master_key, title_kek_src);
    return title_kek;
}

// Check if file is a valid XCI
bool is_xci_file(const std::string& path) {
    if (!fs::exists(path)) return false;

    auto size = fs::file_size(path);
    if (size < 0x104) return false;  // must be at least 0x104 bytes

    std::ifstream fin(path, std::ios::binary);
    if (!fin) return false;

    fin.seekg(0x100, std::ios::beg);
    char magic[4] = { 0 };
    fin.read(magic, 4);

    return std::string(magic, 4) == "HEAD";
}

bool is_nsp_file(const std::string& path) {
    std::ifstream f(path, std::ios::binary);
    if (!f) return false;

    char magic[4];
    f.read(magic, 4);
    return std::string(magic, 4) == "PFS0";
}

std::vector<uint8_t> transcode_data(const std::vector<uint8_t>& data, const std::vector<uint8_t>& key) {
    // Use aes_128_ecb_decrypt for transcoding (decryption in this case)
    return aes_128_ecb_decrypt(key, data);
}

std::vector<uint8_t> get_content_key(const NcaHeader& nca_header, const NcaFsHeader & section, const KeyStore& keys) {
    // Check rights_id for non-zero values
    bool rights_id_non_zero = false;
    for (const auto& b : nca_header.rights_id) {
        if (b != 0) {
            rights_id_non_zero = true;
            break;
        }
    }

    if (rights_id_non_zero) {
        std::stringstream ss;
        for (auto b : nca_header.rights_id) {
            ss << std::hex << std::setw(2) << std::setfill('0') << (int)b;
        }
        std::string rights_id_hex = ss.str();

        auto it = keys.titlekeys.find(rights_id_hex);
        if (it == keys.titlekeys.end()) {
            std::cerr << "[FATAL] Missing title key for Rights ID: " << rights_id_hex << "\n";
            std::exit(1);
        }

        std::vector<uint8_t> kek_key = get_title_kek_key(keys, nca_header);
        std::vector<uint8_t> dec_key_area = transcode_data(it->second, kek_key);

        return dec_key_area;
    }

    // Get the key area key
    std::vector<uint8_t> key_area_key = get_key_area_key(keys, nca_header);
    std::vector<uint8_t> dec_key_area = transcode_data(nca_header.key_area, key_area_key);

    // Split the decrypted key area into key slots (each 16 bytes)
    std::vector<std::vector<uint8_t>> keyslots(4);
    for (int i = 0; i < 4; ++i) {
        keyslots[i] = std::vector<uint8_t>(dec_key_area.begin() + i * 16, dec_key_area.begin() + (i + 1) * 16);
    }

    // Find the non-zero key slot (there should be exactly one)
    std::vector<std::pair<int, std::vector<uint8_t>>> non_zero;
    for (int i = 0; i < 4; ++i) {
        if (std::any_of(keyslots[i].begin(), keyslots[i].end(), [](uint8_t b) { return b != 0; })) {
            non_zero.push_back({ i, keyslots[i] });
        }
    }

    if (non_zero.size() != 1) {
        std::cerr << "[FATAL] Expected exactly 1 content key, found " << non_zero.size() << "\n";
        std::exit(1);
    }

    return non_zero[0].second;  // Return the content key (the only non-zero key)
}

void decrypt_aes_ctr_section(
    std::ifstream& fin,
    std::fstream& fout,
    uint64_t nca_offset,
    const NcaHeader& nca_header,
    const NcaFsHeader & section,
    size_t fs_index,
    const KeyStore& keys)
{
    const auto& entry = nca_header.fs_entries[fs_index];

    uint64_t section_offset = entry.start * 0x200ULL;
    uint64_t section_size = (entry.end - entry.start) * 0x200ULL;
    uint64_t abs_offset = nca_offset + section_offset;

    auto content_key = get_content_key(nca_header, section, keys);
    if (content_key.size() != 16) {
        std::cerr << "[FATAL] content_key must be 16 bytes\n";
        std::exit(1);
    }

    std::array<uint8_t, 16> key{};
    std::copy(content_key.begin(), content_key.end(), key.begin());

    std::cout << "        [*] Decrypting RomFS - AesCtr\n";
    std::cout << "            nca offset: 0x" << std::hex << nca_offset << "\n";
    std::cout << "            Section offset: 0x" << section_offset << "\n";
    std::cout << "            File offset: 0x" << abs_offset << "\n";
    std::cout << "            Size: 0x" << section_size << "\n";
    std::cout << "            KeyGeneration: 0x" << int(nca_header.keygen) << "\n";

    std::vector<uint8_t> enc;

    uint64_t remaining = section_size;
    uint64_t offset_in_section = 0;

    while (remaining > 0) {
        size_t chunk = std::min<uint64_t>(CHUNK_SIZE, remaining);
        if (enc.size() != chunk) {
            enc.resize(chunk);
        }

        fin.seekg(abs_offset + offset_in_section, std::ios::beg);
        fin.read(reinterpret_cast<char*>(enc.data()), chunk);

        if (size_t(fin.gcount()) != chunk) {
            std::cerr << "[FATAL] Short read while decrypting RomFS\n";
            std::exit(1);
        }

        std::vector<uint8_t> dec = aes_ctr_decrypt(enc, content_key, section, section_offset + offset_in_section);

        // Write the decrypted chunk to the output file
        fout.seekp(abs_offset + offset_in_section, std::ios::beg);
        std::cout << "[INFO] Writing 0x" << std::hex << dec.size() << " bytes at 0x" << std::hex << (abs_offset + offset_in_section) << std::endl;
        fout.write(reinterpret_cast<char*>(dec.data()), dec.size());

        // Update positions for the next chunk
        offset_in_section += chunk;
        remaining -= chunk;
    }

    std::cout << "        [*] RomFS AES-CTR decryption complete\n";
}

void build_ctr_ex(
    uint8_t ctr[16],
    uint32_t generation,
    const std::array<uint8_t, 4>& secure_value,
    uint64_t byte_offset)
{
    uint64_t upper =
        uint64_t(generation) |
        ((uint64_t)read_u32_le(secure_value.data()) << 32);

    uint64_t lower = byte_offset >> 4; // divide by 16

    write_u64_be(ctr + 0, upper);
    write_u64_be(ctr + 8, lower);
}

void ctr_ex_crypt_buffer(
    uint8_t* data,
    uint64_t size,
    uint32_t generation,
    uint64_t section_offset,
    const std::array<uint8_t, 4>& secure_value,
    const std::array<uint8_t, 16>& key)
{
    mbedtls_aes_context aes;
    mbedtls_aes_init(&aes);
    mbedtls_aes_setkey_enc(&aes, key.data(), 128);

    for (uint64_t i = 0; i < size; i += 16)
    {
        uint64_t block = section_offset + i;

        uint8_t ctr[16];
        build_ctr_ex(ctr, generation, secure_value, block);

        uint8_t ks[16];
        mbedtls_aes_crypt_ecb(&aes, MBEDTLS_AES_ENCRYPT, ctr, ks);

        size_t n = std::min<uint64_t>(16, size - i);
        for (size_t j = 0; j < n; j++)
            data[i + j] ^= ks[j];
    }

    mbedtls_aes_free(&aes);
}

void ctr_ex_crypt(
    std::istream & in,
    std::ostream & out,
    uint64_t physical_offset,          // where encrypted data lives in NCA
    uint64_t size,                     // bytes to process
    uint32_t generation,               // from BKTR entry
    uint64_t counter_base_offset,      // entry offset base
    const std::array<uint8_t, 4>&secure_value,
    const std::array<uint8_t, 16>&key)
{

    std::cout << "CTR_EX start\n"
        << "  physical_offset = 0x" << std::hex << physical_offset << "\n"
        << "  size            = 0x" << size << "\n"
        << "  generation      = " << std::dec << generation << "\n"
        << "  counter_base    = 0x" << std::hex << counter_base_offset << "\n"
        << std::dec;

    mbedtls_aes_context aes;
    mbedtls_aes_init(&aes);
    mbedtls_aes_setkey_enc(&aes, key.data(), 128);

    const size_t BUF_SIZE = 0x4000;
    std::vector<uint8_t> buf(BUF_SIZE);

    uint64_t processed = 0;

    in.seekg(physical_offset);
    out.seekp(physical_offset);

    while (processed < size)
    {
        size_t chunk = std::min<uint64_t>(BUF_SIZE, size - processed);
        in.read(reinterpret_cast<char*>(buf.data()), chunk);

        for (size_t i = 0; i < chunk; i += 16)
        {
            uint64_t byte_pos =
                counter_base_offset +
                processed +
                i;

            uint8_t ctr[16];
            build_ctr_ex(
                ctr,
                generation,
                secure_value,
                byte_pos
            );

            uint8_t keystream[16];
            mbedtls_aes_crypt_ecb(
                &aes,
                MBEDTLS_AES_ENCRYPT,
                ctr,
                keystream
            );

            size_t block = std::min<size_t>(16, chunk - i);
            for (size_t j = 0; j < block; j++)
                buf[i + j] ^= keystream[j];
        }

        std::cout << "Writing 0x"
            << std::hex << (buf.size())
            << " bytes at 0x" << (physical_offset + processed)
            << std::dec << "\n";
        if ((physical_offset + processed) == 0x2e25b740)
        {
            __debugbreak();
        }
        out.write(reinterpret_cast<char*>(buf.data()), chunk);
        processed += chunk;
    }

    mbedtls_aes_free(&aes);
}

struct CtrExSubsection {
    uint64_t offset;
    uint32_t ctr_seed;
};

std::vector<CtrExSubsection> process_ctr_ex_table(
    std::istream& fin,
    std::ostream& fout,
    uint64_t table_phys,
    uint64_t table_size,
    uint64_t table_rel,                // section-relative offset for IV
    const NcaFsHeader& section,
    const std::array<uint8_t, 16>& key)
{
    uint32_t generation = read_u32_le(section.Generation.data());

    // Read the entire encrypted table
    std::vector<uint8_t> data(table_size);
    fin.seekg(table_phys);
    fin.read(reinterpret_cast<char*>(data.data()), table_size);

    std::array<uint8_t, 4> secure4;
    std::copy_n(section.SecureValue.begin(), 4, secure4.begin());

    // Decrypt table in-place using CTR-EX base stream
    ctr_ex_crypt_buffer(data.data(), table_size, generation, table_rel, secure4, key);

    // -----------------------------
    // Parse BKTR subsection table
    // -----------------------------
    const uint8_t* p = data.data();

    // -------------------------------------------------
    // Read header
    // -------------------------------------------------
    uint32_t bucket_count = read_u32_le(p + 0x4);
    // uint64_t total_physical_size = read_u64_le(p + 0x8); // optional
    const uint8_t* bucket_base_table = p + 0x10;           // 0x10 → 0x3FF0

    // -------------------------------------------------
    // Iterate buckets
    // -------------------------------------------------
    std::vector<CtrExSubsection> out;
    for (uint32_t b = 0; b < bucket_count; b++)
    {
        // Base physical offset for this bucket
        uint64_t physical_offset = read_u64_le(bucket_base_table + (b * 8));

        // Subsection bucket starts at 0x4000 + b*0x4000
        const uint8_t* subsection_bucket = p + 0x4000 + (b * 0x4000);

        uint32_t entry_count = read_u32_le(subsection_bucket + 0x4);
        // uint64_t bucket_end = read_u64_le(subsection_bucket + 0x8); // optional

        const uint8_t* entry_ptr = subsection_bucket + 0x10;

        for (uint32_t i = 0; i < entry_count; i++)
        {
            CtrExSubsection s{};
            s.offset = read_u64_le(entry_ptr + 0);   // Address in Patch RomFS
            s.ctr_seed = read_u32_le(entry_ptr + 0xC); // CTR value for subsection

            out.push_back(s);

            entry_ptr += 0x10; // each entry is 16 bytes
        }
    }

    return out;
}

void decrypt_aes_ctr_ex_section(
    std::ifstream& fin,
    std::fstream& fout,
    uint64_t nca_offset,
    const NcaHeader& nca_header,
    const NcaFsHeader& section,
    size_t fs_index,
    const KeyStore& keys)
{
    // Step 0: Get content key
    auto key_vec = get_content_key(nca_header, section, keys);
    std::array<uint8_t, 16> key;
    std::copy(key_vec.begin(), key_vec.begin() + 16, key.begin());

    // FS offsets
    uint64_t fs_off = SectorToByte(nca_header.fs_entries[fs_index].start);
    uint64_t fs_end = SectorToByte(nca_header.fs_entries[fs_index].end);
    uint64_t fs_size = fs_end - fs_off;

    uint64_t physical_base = nca_offset + fs_off;

    const auto& patch = section.patch_info;
    uint32_t base_generation = read_u32_le(section.Generation.data());

    // -------------------------------------------------
    // CASE 1: No CTR-EX table → normal CTR
    // -------------------------------------------------
    if (!patch.has_aes_ctr_ex_table())
    {
        ctr_ex_crypt(
            fin,
            fout,
            physical_base,
            fs_size,
            base_generation,
            fs_off,
            section.SecureValue,
            key
        );
        return;
    }

    // -------------------------------------------------
    // CASE 2: Decrypt AES-CTR-EX metadata table first
    // -------------------------------------------------
    if (patch.has_aes_ctr_ex_table())
    {
        uint64_t ctr_ex_offset = patch.aes_ctr_ex_offset;
        uint64_t ctr_ex_size = patch.aes_ctr_ex_size;

        std::vector<uint8_t> ctr_ex_data(ctr_ex_size);
        fin.seekg(physical_base + ctr_ex_offset);
        fin.read(reinterpret_cast<char*>(ctr_ex_data.data()), ctr_ex_size);
        if (static_cast<uint64_t>(fin.gcount()) != ctr_ex_size)
            throw std::runtime_error("CTR-EX table short read");

        std::array<uint8_t, 4> secure4;
        std::copy_n(section.SecureValue.begin(), 4, secure4.begin());

        ctr_ex_crypt_buffer(
            ctr_ex_data.data(),
            ctr_ex_size,
            base_generation,
            fs_off + ctr_ex_offset,
            secure4,
            key
        );

        fout.seekp(physical_base + ctr_ex_offset);
        std::cout << "Writing CTR-EX table 0x"
            << std::hex << ctr_ex_size
            << " bytes at 0x" << (physical_base + ctr_ex_offset)
            << std::dec << "\n";
        fout.write(reinterpret_cast<char*>(ctr_ex_data.data()), ctr_ex_size);
    }

    // -------------------------------------------------
    // CASE 3: Decrypt indirect table
    // -------------------------------------------------
    if (patch.has_indirect_table())
    {
        uint64_t indirect_offset = patch.indirect_offset;
        uint64_t indirect_size = patch.indirect_size;

        std::vector<uint8_t> indirect_data(indirect_size);
        fin.seekg(physical_base + indirect_offset);
        fin.read(reinterpret_cast<char*>(indirect_data.data()), indirect_size);
        if (static_cast<uint64_t>(fin.gcount()) != indirect_size)
            throw std::runtime_error("Indirect table short read");

        std::array<uint8_t, 4> secure4;
        std::copy_n(section.SecureValue.begin(), 4, secure4.begin());

        ctr_ex_crypt_buffer(
            indirect_data.data(),
            indirect_size,
            section.Generation[0],        // assuming single generation
            fs_off + indirect_offset,
            secure4,
            key
        );

        fout.seekp(physical_base + indirect_offset);
        std::cout << "Writing indirect table 0x"
            << std::hex << indirect_size
            << " bytes at 0x" << (physical_base + indirect_offset)
            << std::dec << "\n";
        fout.write(reinterpret_cast<char*>(indirect_data.data()), indirect_size);
    }

    // -------------------------------------------------
    // CASE 4: Subsection table + data blocks
    // -------------------------------------------------
    uint64_t table_phys = physical_base + patch.aes_ctr_ex_offset;

    auto subs = process_ctr_ex_table(
        fin,
        fout,
        table_phys,
        patch.aes_ctr_ex_size,
        patch.aes_ctr_ex_offset + fs_off,
        section,
        key
    );

    // -------------------------------------------------
    // Decrypt each region
    // -------------------------------------------------

    for (size_t i = 0; i < subs.size(); i++)
    {
        const auto& s = subs[i];
        uint64_t region_start = s.offset;
        uint64_t region_end =
            (i + 1 < subs.size())
            ? subs[i + 1].offset
            : fs_size;                 // last region goes to end of FS

        uint64_t region_size = region_end - region_start;

        ctr_ex_crypt(
            fin,
            fout,
            physical_base + s.offset,
            region_size,
            s.ctr_seed,
            fs_off + s.offset,
            section.SecureValue,
            key
        );
    }
}

void decrypt_romfs(
    std::ifstream& fin,
    std::fstream& fout,
    uint64_t nca_offset,
    const NcaHeader& nca_header,
    const NcaFsHeader & section,
    size_t fs_index,
    const KeyStore& keys)
{
    switch (section.encryption_type) {

    case 2: // AesXts
        std::cerr << "[FATAL] AesXts RomFS decryption not implemented yet\n";
        std::exit(1);
        break;

    case 3: // AesCtr
        decrypt_aes_ctr_section(
            fin,
            fout,
            nca_offset,
            nca_header,
            section,
            fs_index,
            keys
        );
        break;

    case 4: // AesCtrEx
        decrypt_aes_ctr_ex_section(
            fin,
            fout,
            nca_offset,
            nca_header,
            section,
            fs_index,
            keys
        );
        break;
    default:
        std::cerr << "[FATAL] Unknown encryption type: "
            << int(section.encryption_type) << "\n";
        std::exit(1);
    }
}

void decrypt_pfs0_file_inplace(
    std::ifstream& fin,
    std::fstream& fout,
    const std::string& name,
    uint64_t file_offset,
    uint64_t file_size,
    uint64_t abs_offset,
    uint64_t section_offset,
    uint64_t hash_region_size,
    uint64_t metadata_size,
    const std::vector<uint8_t>& content_key,
    const NcaFsHeader& section)
{
    const uint64_t file_data_base_abs = abs_offset + hash_region_size + metadata_size;
    const uint64_t file_data_base_ctr = section_offset + hash_region_size + metadata_size;

    const uint64_t file_abs = file_data_base_abs + file_offset;
    const uint64_t file_ctr = file_data_base_ctr + file_offset;

    uint64_t remaining = file_size;
    uint64_t processed = 0;

    std::cout << "            decrypting " << name << " ...\n";

    const uint64_t AES_BLOCK = 0x10;

    while (remaining > 0)
    {
        uint64_t chunk = std::min<uint64_t>(CHUNK_SIZE, remaining);

        uint64_t target_abs = file_abs + processed;
        uint64_t target_ctr = file_ctr + processed;

        uint64_t aligned_start = target_abs & ~(AES_BLOCK - 1);
        uint64_t prefix = target_abs - aligned_start;

        uint64_t aligned_size = prefix + chunk;
        aligned_size = (aligned_size + AES_BLOCK - 1) & ~(AES_BLOCK - 1);

        uint64_t aligned_ctr = target_ctr - prefix;

        // --- read aligned encrypted data ---
        fin.seekg(aligned_start, std::ios::beg);

        std::vector<uint8_t> enc(aligned_size);
        fin.read(reinterpret_cast<char*>(enc.data()), aligned_size);

        if (static_cast<uint64_t>(fin.gcount()) != aligned_size)
            throw std::runtime_error("Short read during aligned decrypt");

        // --- decrypt ---
        std::vector<uint8_t> dec =
            aes_ctr_decrypt(enc, content_key, section, aligned_ctr);

        // --- write only requested region ---
        fout.seekp(target_abs, std::ios::beg);
        std::cout << "Writing 0x"
            << std::hex << (prefix + chunk)
            << " bytes at 0x" << target_abs
            << std::dec << "\n";
        fout.write(reinterpret_cast<char*>(dec.data() + prefix), chunk);

        processed += chunk;
        remaining -= chunk;
    }
}


void decrypt_partition_table(
    std::ifstream& fin,
    std::fstream& fout,
    uint64_t nca_offset,
    const NcaHeader& nca_header,
    const NcaFsHeader& section,
    int fs_index,
    KeyStore& keys)
{
    const FsEntry& entry = nca_header.fs_entries[fs_index];

    uint64_t section_offset = entry.start * 0x200ULL;
    uint64_t section_size = (entry.end - entry.start) * 0x200ULL;
    uint64_t abs_offset = nca_offset + section_offset;
    uint64_t hash_region_size = section.hash_region_size();

    std::cout << "        [*] Decrypting PartitionFS @ 0x"
        << std::hex << abs_offset
        << " size=0x" << section_size << "\n";

    if (section.encryption_type == 1) {
        std::cout << "        [*] Section is not encrypted (type 1), skipping decryption\n";
        return;
    }
    else if (section.encryption_type != 3) {
        throw std::runtime_error("PartitionFS encryption type not supported");
    }

    auto content_key = get_content_key(nca_header, section, keys);

    uint64_t data_offset = section_offset + hash_region_size + nca_offset;

    // --- read first 0x10 bytes ---
    fin.seekg(data_offset, std::ios::beg);
    std::vector<uint8_t> enc(0x10);
    fin.read(reinterpret_cast<char*>(enc.data()), enc.size());

    auto dec = aes_ctr_decrypt(enc, content_key, section, section_offset + hash_region_size);

    std::string magic(reinterpret_cast<char*>(dec.data()), 4);
    std::cout << "            FS magic: " << magic << "\n";

    if (magic != "PFS0" && magic != "HFS0") {
        throw std::runtime_error("Invalid PartitionFS magic");
    }

    uint32_t file_count = read_u32_le(dec.data() + 0x04);
    uint32_t string_table_size = read_u32_le(dec.data() + 0x08);

    uint32_t entry_size = (magic == "PFS0") ? 0x18 : 0x40;

    uint64_t header_size = 0x10;
    uint64_t entries_size = file_count * entry_size;
    uint64_t metadata_size = header_size + entries_size + string_table_size;

    // --- decrypt metadata ---
    fin.seekg(data_offset, std::ios::beg);
    std::vector<uint8_t> enc_meta(metadata_size);
    fin.read(reinterpret_cast<char*>(enc_meta.data()), enc_meta.size());

    auto dec_meta = aes_ctr_decrypt(enc_meta, content_key, section, section_offset + hash_region_size);

    fout.seekp(data_offset, std::ios::beg);
    std::cout << "[INFO] Writing 0x" << std::hex << dec_meta.size() << " bytes at 0x" << std::hex << (data_offset) << std::endl;
    fout.write(reinterpret_cast<char*>(dec_meta.data()), dec_meta.size());

    if (magic == "HFS0") {
        throw std::runtime_error("Unhandled partitionFS magic HFS0");
    }

    const auto& buf = dec_meta;

    uint64_t entry_table_offset = header_size;
    uint64_t string_table_offset = entry_table_offset + file_count * entry_size;

    struct Entry {
        uint64_t offset;
        uint64_t size;
        uint32_t name_offset;
    };

    std::vector<Entry> entries;

    for (uint32_t i = 0; i < file_count; ++i) {
        uint64_t base = entry_table_offset + i * entry_size;

        Entry e;
        e.offset = read_u64_le(buf.data() + base);
        e.size = read_u64_le(buf.data() + base + 8);
        e.name_offset = read_u32_le(buf.data() + base + 16);

        entries.push_back(e);
    }

    const uint8_t* string_table = buf.data() + string_table_offset;

    std::cout << "        [*] Files:\n";

    for (const auto& e : entries) {
        const char* name = reinterpret_cast<const char*>(string_table + e.name_offset);

        decrypt_pfs0_file_inplace(
            fin, fout,
            name,
            e.offset,
            e.size,
            abs_offset,
            section_offset,
            hash_region_size,
            metadata_size,
            content_key,
            section);
    }

    std::cout << "        [*] PartitionFS fully decrypted\n";
}

void decrypt_nca(std::ifstream& fin, std::fstream& fout, const Partition& partition, KeyStore& keys) {
    uint64_t nca_offset = partition.hfs0_offset + partition.offset;
    std::cout << "[INFO] Decrypt NCA Start for " << partition.name
        << " at 0x" << std::hex << nca_offset << "\n";

    // Seek and read header
    fin.seekg(nca_offset, std::ios::beg);
    std::vector<uint8_t> header(0xC00);
    fin.read(reinterpret_cast<char*>(header.data()), header.size());
    if (fin.gcount() != static_cast<std::streamsize>(header.size())) {
        std::cerr << "[!] Failed to read full NCA header\n";
        return;
    }

    NcaHeader nca_header = parse_nca_header(header);
    bool encrypted = false;

    // Check magic
    std::string magic(nca_header.magic, 4);
    if (magic != "NCA3" && magic != "NCA2") {
        if (keys.keys.find("header_key") == keys.keys.end()) {
            std::cerr << "[FATAL] Missing 'header_key' in key file\n";
            std::exit(1);
        }
        std::vector<uint8_t>& header_key = keys.keys["header_key"];
        if (header_key.size() != 32) {
            std::cerr << "[FATAL] header_key must be 32 bytes\n";
            std::exit(1);
        }

        std::vector<uint8_t> header_bytes(header.begin(), header.end());
        auto dec = aes_xts_decrypt(header_bytes, header_key, 0);
        nca_header = parse_nca_header(dec);

        std::string new_magic(nca_header.magic, 4);

        std::cout << "[INFO] Decrypted magic: " << new_magic << "\n";

        if (new_magic != "NCA3" && new_magic != "NCA2") {
            std::cerr << "[FATAL] Not a valid NCA header after decryption\n";
            std::exit(1);
        }

        std::copy(dec.begin(), dec.end(), header.begin());
        encrypted = true;

        // Patch magic
        dec[0x200] = 'D'; dec[0x201] = 'N';
        dec[0x202] = 'C'; dec[0x203] = 'A';
        dec[0x206] = 1;

        fout.seekp(nca_offset, std::ios::beg);
        std::cout << "[INFO] Patched header written at 0x" << std::hex << nca_offset << " size: 0x" << std::hex << dec.size() << "\n";
        fout.write(reinterpret_cast<char*>(dec.data()), dec.size());
    }

    // Process FS entries
    for (int i = 0; i < 4; ++i) {
        FsEntry& entry = nca_header.fs_entries[i];
        uint64_t fs_header_offset = 0x400 + i * 0x200;

        fout.seekp(nca_offset + fs_header_offset + 0x04, std::ios::beg);
        char one = 1;
        std::cout << "[INFO] Wrote 0x1 at 0x" << std::hex << (nca_offset + fs_header_offset + 0x04) << "\n";
        fout.write(&one, 1);

        if (entry.end <= entry.start) continue;

        std::cout << "[INFO] Section " << i
            << " start=0x" << std::hex << entry.start
            << " end=0x" << entry.end
            << " size=0x" << (entry.end - entry.start) << "\n";

        NcaFsHeader section = parse_nca_fs_header(std::vector<char>(header.begin() + fs_header_offset, header.begin() + fs_header_offset + 0x200));
        if (section.fs_type == 0) {
            decrypt_romfs(fin, fout, nca_offset, nca_header, section, i, keys);
        }
        else if (section.fs_type == 1) {
            decrypt_partition_table(fin, fout, nca_offset, nca_header, section, i, keys);
        }
        else {
            std::cerr << "[FATAL] Unknown partition type: " << section.fs_type << "\n";
            std::exit(1);
        }
    }

    std::cout << "[INFO] Decrypt NCA Stop for " << partition.name << "\n";
}

// ---------------- Parse HFS0 Partitions ----------------
std::vector<Partition> parse_hfs0_partitions(std::ifstream& fin, uint64_t hfs0_offset) {
    std::cout << "[INFO] parse_hfs0_partitions at 0x" << std::hex << hfs0_offset << "\n";
    fin.seekg(hfs0_offset, std::ios::beg);

    char magic[4];
    fin.read(magic, 4);
    if (std::string(magic, 4) != "HFS0") {
        throw std::runtime_error("Invalid HFS0 magic at offset " + std::to_string(hfs0_offset));
    }

    uint32_t file_count;
    uint32_t string_table_size;
    fin.read(reinterpret_cast<char*>(&file_count), 4);
    fin.read(reinterpret_cast<char*>(&string_table_size), 4);

    const uint64_t PartitionFsHeader_Size = 0x10;
    const uint64_t ENTRY_SIZE = 0x40;
    uint64_t string_table_offset = PartitionFsHeader_Size + (file_count * ENTRY_SIZE);
    uint64_t file_data_region = string_table_offset + string_table_size;

    fin.seekg(4, std::ios::cur); // Skip reserved

    std::cout << "[INFO] Found " << std::dec << file_count << " partitions\n";
    std::cout << "[INFO] String table size: 0x" << std::hex << string_table_size << "\n";
    std::cout << "[INFO] file_data_region: 0x" << std::hex << file_data_region << "\n";

    struct Entry { uint64_t rel_offset; uint64_t size; uint32_t str_offset; };
    std::vector<Entry> entries;

    for (uint32_t i = 0; i < file_count; ++i) {
        std::vector<char> entry_buf(ENTRY_SIZE);
        fin.read(entry_buf.data(), ENTRY_SIZE);

        uint64_t rel_offset = *reinterpret_cast<uint64_t*>(entry_buf.data());
        uint64_t size = *reinterpret_cast<uint64_t*>(entry_buf.data() + 8);
        uint32_t str_offset = *reinterpret_cast<uint32_t*>(entry_buf.data() + 16);
        entries.push_back({ rel_offset, size, str_offset });
    }

    std::vector<Partition> partitions;
    uint64_t string_table_base = hfs0_offset + string_table_offset;

    for (auto& e : entries) {
        fin.seekg(string_table_base + e.str_offset, std::ios::beg);
        std::string name;
        char c;
        while (fin.get(c) && c != '\0') {
            name += c;
        }
        partitions.push_back({ name, hfs0_offset, e.rel_offset, e.rel_offset + file_data_region, e.size });
    }

    return partitions;
}

void load_ticket(
    std::ifstream& fin,
    const Partition& part,
    KeyStore& keys,
    uint64_t hfs0_offset,
    uint64_t offset)
{
    std::cout << "        [*] Loading ticket " << part.name << "\n";

    std::cout << "hfs0_offset: 0x" << std::hex << hfs0_offset
        << " offset: 0x" << offset << "\n";

    std::cout << "part[offset]: 0x" << part.offset
        << " size: 0x" << part.size << "\n";

    fin.seekg(hfs0_offset + offset + part.offset, std::ios::beg);

    std::vector<uint8_t> raw(part.size);
    fin.read(reinterpret_cast<char*>(raw.data()), raw.size());

    if (fin.gcount() < 4) {
        std::cerr << "        [!] Ticket too small\n";
        return;
    }

    uint32_t sig_type =
        raw[0] |
        (raw[1] << 8) |
        (raw[2] << 16) |
        (raw[3] << 24);

    size_t data_offset;

    if (sig_type == 0x10000 || sig_type == 0x10003) {
        data_offset = 0x240; // RSA4096
    }
    else if (sig_type == 0x10001 || sig_type == 0x10004) {
        data_offset = 0x140; // RSA2048
    }
    else if (sig_type == 0x10002 || sig_type == 0x10005) {
        data_offset = 0x80;  // ECDSA
    }
    else {
        std::cerr << "        [!] Unknown ticket signature type 0x"
            << std::hex << sig_type << "\n";
        return;
    }

    if (raw.size() < data_offset + 0x180) {
        std::cerr << "        [!] Ticket truncated\n";
        return;
    }

    std::vector<uint8_t> title_key(
        raw.begin() + data_offset + 0x40,
        raw.begin() + data_offset + 0x50);

    std::vector<uint8_t> rights_id(
        raw.begin() + data_offset + 0x160,
        raw.begin() + data_offset + 0x170);

    std::vector<uint8_t> ticket_id(
        raw.begin() + data_offset + 0x150,
        raw.begin() + data_offset + 0x158);

    // Convert rights_id to hex string
    std::ostringstream ss;
    ss << std::hex << std::setfill('0');
    for (uint8_t b : rights_id)
        ss << std::setw(2) << (int)b;
    std::string rights_hex = ss.str();

    std::cout << "        rights_id = " << rights_hex << "\n";

    std::cout << "        title_key = ";
    for (uint8_t b : title_key)
        std::cout << std::hex << std::setw(2) << std::setfill('0') << (int)b;
    std::cout << "\n";

    std::cout << "        ticket_id = ";
    for (uint8_t b : ticket_id)
        std::cout << std::hex << std::setw(2) << std::setfill('0') << (int)b;
    std::cout << "\n";


    // Store encrypted titlekey
    keys.titlekeys[rights_hex] = title_key;
}

// ---------------- decrypt_partition ----------------
void decrypt_partition(std::ifstream& fin, std::fstream& fout,
    uint64_t hfs0_offset, uint64_t offset,
    uint64_t size, const std::string& name,
    KeyStore& keys) {
    std::cout << "[INFO] decrypt_partition called for " << name
        << " at 0x" << std::hex << (hfs0_offset + offset)
        << " size 0x" << size << "\n";

    // Peek magic at offset
    fin.seekg(hfs0_offset + offset, std::ios::beg);
    char magic[4] = { 0 };
    fin.read(magic, 4);

    if (std::string(magic, 4) == "HFS0") {
        // Parse partitions
        auto partitions = parse_hfs0_partitions(fin, hfs0_offset + offset);
        for (auto& p : partitions) {
            if (p.name.size() >= 4 && p.name.substr(p.name.size() - 4) == ".tik") {
                load_ticket(fin, p, keys, hfs0_offset, offset);
            }
        }
        for (auto& p : partitions) {
            if (p.name.size() >= 4 && p.name.substr(p.name.size() - 4) == ".nca") {
                decrypt_nca(fin, fout, p, keys);
            }
        }
    }
}

std::string convert_nsp(const std::string& input_path,
    const std::string& output_dir,
    const std::string& name,
    KeyStore& keys)
{
    fs::path output_path = fs::path(output_dir) / (name + ".dnsp");

    fs::copy_file(input_path, output_path, fs::copy_options::overwrite_existing);

    std::ifstream fin(input_path, std::ios::binary);
    std::fstream fout(output_path, std::ios::binary | std::ios::in | std::ios::out);

    if (!fin || !fout)
        throw std::runtime_error("Failed to open NSP");

    // Parse root PFS0
    fin.seekg(0, std::ios::beg);

    char magic[4];
    fin.read(magic, 4);
    if (std::string(magic, 4) != "PFS0")
        throw std::runtime_error("Invalid NSP");

    uint32_t file_count;
    uint32_t string_table_size;

    fin.read(reinterpret_cast<char*>(&file_count), 4);
    fin.read(reinterpret_cast<char*>(&string_table_size), 4);

    fin.seekg(4, std::ios::cur); // skip reserved

    struct Entry {
        uint64_t offset;
        uint64_t size;
        uint32_t name_offset;
    };

    std::vector<Entry> entries(file_count);

    for (uint32_t i = 0; i < file_count; i++) {
        fin.read(reinterpret_cast<char*>(&entries[i]), sizeof(Entry));
    }

    uint64_t string_table_offset = 0x10 + file_count * 0x18;
    uint64_t data_offset = string_table_offset + string_table_size;

    // ---- Pass 1: load tickets ----
    for (auto& e : entries) {
        fin.seekg(string_table_offset + e.name_offset);
        std::string name;
        char c;
        while (fin.get(c) && c != '\0') name += c;

        if (name.ends_with(".tik")) {
            Partition fake{
                name,
                0,          // hfs0_offset
                0,
                e.offset + data_offset,
                e.size
            };

            load_ticket(fin, fake, keys, 0, 0);
        }
    }

    // ---- Pass 2: decrypt NCAs ----
    for (auto& e : entries) {
        fin.seekg(string_table_offset + e.name_offset);
        std::string name;
        char c;
        while (fin.get(c) && c != '\0') name += c;

        if (name.ends_with(".nca")) {
            Partition fake{
                name,
                0,
                0,
                e.offset + data_offset,
                e.size
            };

            decrypt_nca(fin, fout, fake, keys);
        }
    }

    return output_path.string();
}

// ---------------- Convert XCI ----------------
std::string convert_xci(const std::string& input_path, const std::string& output_dir, const std::string& name, KeyStore& keys) {
    const std::string new_ext = ".dxci";
    fs::path output_path = fs::path(output_dir) / (name + new_ext);

    // Overwrite prompt
    if (fs::exists(output_path)) {
        std::cout << output_path << " already exists. Overwrite? [y/N]: ";
        std::string answer;
        std::cin >> answer;
        if (answer != "y" && answer != "Y") {
            throw std::runtime_error("Operation cancelled by user.");
        }
        fs::remove(output_path);
    }

    fs::create_directories(output_dir);
    fs::copy_file(input_path, output_path);

    std::ifstream fin(input_path, std::ios::binary);
    std::fstream fout(output_path, std::ios::binary | std::ios::in | std::ios::out);

    if (!fin || !fout) throw std::runtime_error("Failed to open input/output files.");

    // Verify HEAD magic
    fin.seekg(0x100, std::ios::beg);
    char magic[4];
    fin.read(magic, 4);
    if (std::string(magic, 4) != "HEAD") {
        throw std::runtime_error("Invalid XCI magic number.");
    }

    // Read HFS0 offset/size
    fin.seekg(0x130, std::ios::beg);
    uint64_t hfs0_offset;
    fin.read(reinterpret_cast<char*>(&hfs0_offset), 8);

    fin.seekg(0x138, std::ios::beg);
    uint64_t hfs0_size;
    fin.read(reinterpret_cast<char*>(&hfs0_size), 8);

    std::cout << "[INFO] HFS0PartitionOffset: 0x" << std::hex << hfs0_offset << "\n";
    std::cout << "[INFO] HFS0HeaderSize:      0x" << std::hex << hfs0_size << "\n";

    // Overwrite HEAD -> DXCI
    fout.seekp(0x100, std::ios::beg);
    std::cout << "[INFO] Wrote DXCI magic at 0x" << std::hex << 0x100 << " size: 0x" << std::hex << 4 << "\n";
    fout.write("DXCI", 4);

    // Parse partitions
    auto partitions = parse_hfs0_partitions(fin, hfs0_offset);

    // Process partitions (dummy decrypt)
    for (auto& p : partitions) {
        std::cout << "[INFO] Partition: " << p.name
            << ", rel_offset=0x" << std::hex << p.rel_offset
            << ", offset=0x" << std::hex << p.offset
            << ", size=0x" << std::hex << p.size << "\n";

        decrypt_partition(fin, fout, hfs0_offset, p.offset, p.size, p.name, keys);
    }

    return output_path.string();
}

// Convert file, validating type first
std::string convert_file(const std::string& input_path, const std::string& output_dir, KeyStore& keys) {
    std::string base_name = fs::path(input_path).filename().string();
    std::string name = fs::path(base_name).stem().string();

    if (is_xci_file(input_path)) {
        return convert_xci(input_path, output_dir, name, keys);
    }
    
    if (is_nsp_file(input_path)) {
        return convert_nsp(input_path, output_dir, name, keys);
    }

    throw std::runtime_error("Unsupported file type. Only valid XCI files are supported.");
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <input_file> <output_dir> <key_file>\n";
        return 1;
    }

    std::string input_file = argv[1];
    std::string output_dir = argv[2];
    std::string key_file = argv[3];

    try {
        KeyStore ks = load_keys(key_file);
        std::string new_file = convert_file(input_file, output_dir, ks);
        std::cout << "Created: " << new_file << std::endl;
    }
    catch (const std::exception& e) {
        std::cerr << "[ERROR] " << e.what() << std::endl;
        return 1;
    }

    return 0;
}
