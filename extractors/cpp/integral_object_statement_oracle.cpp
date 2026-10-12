#include <iostream>
#include <stdexcept>
#include <string>

void trace(const std::string &mode, int initial, int delta) {
  int value = initial;
  if (mode == "add") {
    value = value + delta;
  } else if (mode == "branch") {
    value = value != 0 ? delta : delta + 1;
  } else if (mode == "loop") {
    while (value > 0)
      --value;
  } else if (mode == "for") {
    value = delta;
    for (; value > 0; --value) {
    }
  } else if (mode == "break") {
    while (value > 0) {
      --value;
      break;
    }
  } else if (mode == "continue") {
    while (value > 0) {
      --value;
      continue;
    }
  } else if (mode == "do") {
    do {
      --value;
    } while (value > 0);
  } else if (mode == "do_continue") {
    do {
      --value;
      continue;
    } while (value > 0);
  } else if (mode == "for_continue") {
    value = 3;
    for (; value > 0; --value) {
      --value;
      continue;
    }
  } else if (mode == "sequence") {
    value = value + delta;
    value = -value;
  } else {
    throw std::runtime_error("unknown integral object statement mode");
  }
  std::cout << "s32 " << value << '\n';
}

int main() {
  std::string mode;
  int initial;
  int delta;
  while (std::cin >> mode >> initial >> delta)
    trace(mode, initial, delta);
}
