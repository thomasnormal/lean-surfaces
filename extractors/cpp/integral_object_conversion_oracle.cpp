#include <cstdint>
#include <iostream>
#include <limits>
#include <string>
#include <type_traits>

template <typename Value>
Value parse(const std::string &text) {
  if constexpr (std::is_same_v<Value, bool>)
    return std::stoll(text) != 0;
  else if constexpr (std::is_signed_v<Value>)
    return static_cast<Value>(std::stoll(text));
  else
    return static_cast<Value>(std::stoull(text));
}

template <typename Destination, typename Source>
void trace(const std::string &destination, const std::string &initial,
           const std::string &replacement) {
  const Destination initialized = static_cast<Destination>(parse<Source>(initial));
  Destination assigned = initialized;
  assigned = static_cast<Destination>(parse<Source>(replacement));
  std::cout << destination << ' ';
  if constexpr (std::is_same_v<Destination, bool>)
    std::cout << (assigned ? 1 : 0);
  else if constexpr (std::is_signed_v<Destination>)
    std::cout << static_cast<std::int64_t>(assigned);
  else
    std::cout << static_cast<std::uint64_t>(assigned);
  std::cout << '\n';
}

template <typename Destination>
void source(const std::string &destination, const std::string &sourceFormat,
            const std::string &initial, const std::string &replacement) {
  if (sourceFormat == "b") trace<Destination, bool>(destination, initial, replacement);
  else if (sourceFormat == "s8") trace<Destination, signed char>(destination, initial, replacement);
  else if (sourceFormat == "u8") trace<Destination, unsigned char>(destination, initial, replacement);
  else if (sourceFormat == "s16") trace<Destination, short>(destination, initial, replacement);
  else if (sourceFormat == "u16") trace<Destination, unsigned short>(destination, initial, replacement);
  else if (sourceFormat == "s32") trace<Destination, int>(destination, initial, replacement);
  else if (sourceFormat == "u32") trace<Destination, unsigned int>(destination, initial, replacement);
  else if (sourceFormat == "s64") trace<Destination, long long>(destination, initial, replacement);
  else if (sourceFormat == "u64") trace<Destination, unsigned long long>(destination, initial, replacement);
}

void destination(const std::string &destinationFormat, const std::string &sourceFormat,
                 const std::string &initial, const std::string &replacement) {
  if (destinationFormat == "b") source<bool>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "s8") source<signed char>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "u8") source<unsigned char>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "s16") source<short>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "u16") source<unsigned short>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "s32") source<int>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "u32") source<unsigned int>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "s64") source<long long>(destinationFormat, sourceFormat, initial, replacement);
  else if (destinationFormat == "u64") source<unsigned long long>(destinationFormat, sourceFormat, initial, replacement);
}

int main() {
  static_assert(sizeof(short) == 2 && sizeof(int) == 4 && sizeof(long long) == 8);
  std::string destinationFormat, sourceFormat, initial, replacement;
  while (std::cin >> destinationFormat >> sourceFormat >> initial >> replacement)
    destination(destinationFormat, sourceFormat, initial, replacement);
}
