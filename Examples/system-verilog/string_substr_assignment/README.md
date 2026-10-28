# Source-pure string substring assignment

A blocking assignment from `string.substr(i, j)` is admitted when the
receiver's earlier history is a direct ASCII literal and both inclusive bounds
are integral literals. The resulting ASCII history feeds later comparisons;
dynamic, aliased, timed, nonblocking, and non-ASCII forms remain loud.
