print(float(), float(True), float(False), float(9007199254740993))
print(float("0.1"), float("\u3000٠.١\u3000"), float("1_2.3_4e+5_6"))
print(float("-0e999999999999999999999999"))
print(float("-1e-999999999999999999999999"), float("1e999999999999999999999999"))
print(float("2.4703282292062327e-324"), float("2.4703282292062328e-324"))
try:
    float("1._0")
except ValueError:
    print("invalid caught")


def convert(value):
    return float(value)


print(convert("１２.３４e٥"))
