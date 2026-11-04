# Source-pure string NUL write observations

IEEE 1800-2023 section 6.16 ignores an assignment of integral zero to a string
character. This fixture checks that scalar string length and compare queries
still observe the unchanged ASCII history.
