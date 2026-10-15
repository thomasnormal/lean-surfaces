#include "dump_reachability.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <vector>

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  std::size_t chunk;
  try {
    chunk = std::stoul(argv[1]);
  } catch (...) {
    return 2;
  }
  if (chunk == 0)
    return 2;
  std::string input(std::istreambuf_iterator<char>(std::cin), {});
  leancpp::DumpReachability reachability;
  for (std::size_t offset = 0; offset < input.size(); offset += chunk)
    reachability.consume(std::string_view(input).substr(offset, chunk));
  if (!reachability.complete())
    return 1;
  std::vector<std::string> identifiers(reachability.expressionIds().begin(),
                                       reachability.expressionIds().end());
  std::sort(identifiers.begin(), identifiers.end());
  for (const std::string &identifier : identifiers)
    std::cout << identifier << '\n';
}
