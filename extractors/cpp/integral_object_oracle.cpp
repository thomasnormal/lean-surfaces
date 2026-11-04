#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <type_traits>

template <typename Value>
Value parse(const std::string &text) {
  if constexpr (std::is_signed_v<Value>)
    return static_cast<Value>(std::stoll(text));
  else
    return static_cast<Value>(std::stoull(text));
}

template <typename Value>
void emit(const std::string &format, Value value) {
  std::cout << format << ' ';
  if constexpr (std::is_signed_v<Value>)
    std::cout << static_cast<std::int64_t>(value);
  else
    std::cout << static_cast<std::uint64_t>(value);
}

template <typename Value>
void trace(const std::string &format, const std::string &initialText,
           const std::string &replacementText) {
  const Value initial = parse<Value>(initialText);
  const Value replacement = parse<Value>(replacementText);
  Value first;
  Value &alias = first;
  first = initial;
  const Value &readOnly = first;
  const Value distinct = initial;
  emit(format, first);
  std::cout << ' ';
  alias = replacement;
  emit(format, readOnly);
  std::cout << ' ';
  emit(format, distinct);
  std::cout << ' ';
  Value *dynamic = new Value(initial);
  Value &dynamicAlias = *dynamic;
  dynamicAlias = replacement;
  emit(format, *dynamic);
  delete dynamic;
  std::cout << '\n';
}

int main() {
  static_assert(std::numeric_limits<unsigned char>::digits == 8);
  static_assert(std::numeric_limits<short>::digits == 15);
  static_assert(std::numeric_limits<int>::digits == 31);
  static_assert(std::numeric_limits<long>::digits == 63);
  static_assert(std::numeric_limits<long long>::digits == 63);
  std::string format, initial, replacement;
  while (std::cin >> format >> initial >> replacement) {
    if (format == "b") trace<bool>(format, initial, replacement);
    else if (format == "s8") trace<signed char>(format, initial, replacement);
    else if (format == "u8") trace<unsigned char>(format, initial, replacement);
    else if (format == "s16") trace<short>(format, initial, replacement);
    else if (format == "u16") trace<unsigned short>(format, initial, replacement);
    else if (format == "s32") trace<int>(format, initial, replacement);
    else if (format == "u32") trace<unsigned int>(format, initial, replacement);
    else if (format == "s64") trace<long long>(format, initial, replacement);
    else if (format == "u64") trace<unsigned long long>(format, initial, replacement);
    else throw std::runtime_error("unknown integral object format");
  }
}
