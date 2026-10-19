#include "dump_reachability.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <vector>

int main(int argc, char **argv) {
  if (argc != 2 && (argc != 3 || std::string(argv[2]) != "ast"))
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
  const auto &observed = argc == 3 ? reachability.astNodeIds() : reachability.expressionIds();
  std::vector<std::string> identifiers(observed.begin(), observed.end());
  std::sort(identifiers.begin(), identifiers.end());
  for (const std::string &identifier : identifiers)
    std::cout << identifier << '\n';
}
