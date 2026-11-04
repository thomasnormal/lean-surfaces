#include <climits>
#include <type_traits>
#include <utility>

#define SAME(expression, type) \
  static_assert(std::is_same_v<decltype(expression), type>)

static_assert(CHAR_BIT == 8);
static_assert(sizeof(char) * CHAR_BIT == 8);
static_assert(sizeof(short) * CHAR_BIT == 16);
static_assert(sizeof(int) * CHAR_BIT == 32);
static_assert(sizeof(long) * CHAR_BIT == 64);
static_assert(sizeof(long long) * CHAR_BIT == 64);
static_assert(std::is_signed_v<char>);

SAME(+true, int);
SAME(+static_cast<char>(1), int);
SAME(+static_cast<signed char>(1), int);
SAME(+static_cast<unsigned char>(1), int);
SAME(+static_cast<short>(1), int);
SAME(+static_cast<unsigned short>(1), int);
SAME(+static_cast<int>(1), int);
SAME(+static_cast<unsigned int>(1), unsigned int);
SAME(+static_cast<long>(1), long);
SAME(+static_cast<unsigned long>(1), unsigned long);
SAME(+static_cast<long long>(1), long long);
SAME(+static_cast<unsigned long long>(1), unsigned long long);

SAME(static_cast<char>(1) + static_cast<unsigned char>(1), int);
SAME(static_cast<short>(1) + static_cast<unsigned short>(1), int);
SAME(static_cast<int>(1) + static_cast<unsigned int>(1), unsigned int);
SAME(static_cast<int>(1) + static_cast<long>(1), long);
SAME(static_cast<unsigned int>(1) + static_cast<long>(1), long);
SAME(static_cast<long>(1) + static_cast<unsigned int>(1), long);
SAME(static_cast<unsigned long>(1) + static_cast<long long>(1), unsigned long long);
SAME(static_cast<long long>(1) + static_cast<unsigned long>(1), unsigned long long);
SAME(static_cast<long long>(1) + static_cast<unsigned long long>(1), unsigned long long);
SAME(static_cast<unsigned long long>(1) + static_cast<long long>(1), unsigned long long);
SAME(static_cast<unsigned long>(1) + static_cast<long>(1), unsigned long);
SAME(static_cast<unsigned long>(1) + static_cast<unsigned int>(1), unsigned long);

SAME(static_cast<unsigned short>(1) < static_cast<int>(2), bool);
SAME(static_cast<unsigned int>(1) == static_cast<long>(1), bool);
SAME(static_cast<unsigned long>(1) != static_cast<long long>(1), bool);
