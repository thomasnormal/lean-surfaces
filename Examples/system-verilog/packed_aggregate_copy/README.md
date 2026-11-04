# Packed aggregate copies

Direct blocking copies of untagged packed structs and unions use the existing
flat vector state. The extractor admits the whole aggregate as a vector target;
nonblocking, timed, tagged, and unpacked aggregate copies remain loud.
