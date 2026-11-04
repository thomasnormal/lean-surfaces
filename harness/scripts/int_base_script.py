def record(log, tag, value):
    log.append(tag)
    return value


print(int("ff", base=16))
print(int(" \t-0B_1_0\n", 0))
print(int("0_0_0", base=0))
print(int("Zz", 36))
print(int(b"+0o_77", base=0))

log = []
print(int(record(log, 1, "ff"), base=record(log, 2, 16)))
print(log)
try:
    int(record(log, 3, "ff"), base=record(log, 4, 16), other=record(log, 5, 0))
except TypeError:
    print(log)

try:
    int("010", base=0)
except ValueError:
    print("leading zero rejected")

try:
    int("ff", 16, base=1 // 0)
except ZeroDivisionError:
    print("keyword evaluated before arity")
