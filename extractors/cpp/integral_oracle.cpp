#include <cstdint>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <type_traits>

template <typename Value>
void emit(const std::string &format, Value value) {
  std::cout << "ok " << format << ' ';
  if constexpr (std::is_signed_v<Value>)
    std::cout << static_cast<std::int64_t>(value);
  else
    std::cout << static_cast<std::uint64_t>(value);
  std::cout << '\n';
}

template <typename Value>
Value parse(const std::string &text) {
  if constexpr (std::is_signed_v<Value>)
    return static_cast<Value>(std::stoll(text));
  else
    return static_cast<Value>(std::stoull(text));
}

template <typename Callback>
void dispatch(const std::string &format, Callback callback) {
  if (format == "b") callback.template operator()<bool>();
  else if (format == "s8") callback.template operator()<std::int8_t>();
  else if (format == "u8") callback.template operator()<std::uint8_t>();
  else if (format == "s16") callback.template operator()<std::int16_t>();
  else if (format == "u16") callback.template operator()<std::uint16_t>();
  else if (format == "s32") callback.template operator()<std::int32_t>();
  else if (format == "u32") callback.template operator()<std::uint32_t>();
  else if (format == "s64") callback.template operator()<std::int64_t>();
  else if (format == "u64") callback.template operator()<std::uint64_t>();
  else throw std::runtime_error("unknown format");
}

template <typename Value>
void arithmetic(const std::string &operation, const std::string &format,
                Value left, Value right) {
  if (operation == "add") emit(format, left + right);
  else if (operation == "sub") emit(format, left - right);
  else if (operation == "mul") emit(format, left * right);
  else if (operation == "div") emit(format, left / right);
  else if (operation == "rem") emit(format, left % right);
  else if (operation == "and") emit(format, left & right);
  else if (operation == "or") emit(format, left | right);
  else if (operation == "xor") emit(format, left ^ right);
  else if (operation == "eq") emit("b", left == right);
  else if (operation == "ne") emit("b", left != right);
  else if (operation == "lt") emit("b", left < right);
  else if (operation == "le") emit("b", left <= right);
  else if (operation == "gt") emit("b", left > right);
  else if (operation == "ge") emit("b", left >= right);
  else throw std::runtime_error("unknown binary operation");
}

template <typename Value>
void evaluate(const std::string &operation, const std::string &format,
              const std::string &leftText, const std::string &rightFormat,
              const std::string &rightText) {
  const Value left = parse<Value>(leftText);
  if (operation == "plus") emit(format, +left);
  else if (operation == "neg") emit(format, -left);
  else if (operation == "not") emit("b", !left);
  else if (operation == "compl") emit(format, ~left);
  else if (operation == "shl" || operation == "shr") {
    dispatch(rightFormat, [&]<typename Count>() {
      const Count count = parse<Count>(rightText);
      if (operation == "shl") emit(format, left << count);
      else emit(format, left >> count);
    });
  } else arithmetic(operation, format, left, parse<Value>(rightText));
}

int main() {
  static_assert(std::numeric_limits<std::int32_t>::digits == 31);
  static_assert(std::numeric_limits<std::uint32_t>::digits == 32);
  static_assert(std::numeric_limits<std::int64_t>::digits == 63);
  static_assert(std::numeric_limits<std::uint64_t>::digits == 64);
  static_assert(std::is_same_v<decltype(+std::int32_t{}), std::int32_t>);
  static_assert(std::is_same_v<decltype(+std::uint32_t{}), std::uint32_t>);
  static_assert(std::is_same_v<decltype(+std::int64_t{}), std::int64_t>);
  static_assert(std::is_same_v<decltype(+std::uint64_t{}), std::uint64_t>);
  std::string operation, format, leftText, rightFormat, rightText;
  while (std::cin >> operation >> format >> leftText >> rightFormat >> rightText) {
    if (operation == "convert") {
      dispatch(format, [&]<typename Source>() {
        dispatch(rightFormat, [&]<typename Destination>() {
          emit(rightFormat, static_cast<Destination>(parse<Source>(leftText)));
        });
      });
    } else if (operation == "not" && format == "b") {
      emit("b", !parse<bool>(leftText));
    } else if (format == "s32") {
      evaluate<std::int32_t>(operation, format, leftText, rightFormat, rightText);
    } else if (format == "u32") {
      evaluate<std::uint32_t>(operation, format, leftText, rightFormat, rightText);
    } else if (format == "s64") {
      evaluate<std::int64_t>(operation, format, leftText, rightFormat, rightText);
    } else if (format == "u64") {
      evaluate<std::uint64_t>(operation, format, leftText, rightFormat, rightText);
    } else throw std::runtime_error("operation requires a promoted format");
  }
}
