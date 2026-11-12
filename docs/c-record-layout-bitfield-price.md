# C parser-native bit-field layout price

Measured from the pinned Clang record-layout probe on a frozen external manifest.

- files: 12
- fully joined records: 12
- files with bit-fields: 12

| file | size | alignment | bit-fields | offsets / widths |
| --- | ---: | ---: | ---: | --- |
| `20230630-1.c` | 2 | 2 | 5 | i@0/12, c1@12/1, c2@13/1, c3@14/1, c4@15/1 |
| `20230630-2.c` | 2 | 2 | 5 | i@0/12, c1@12/1, c2@13/1, c3@14/1, c4@15/1 |
| `20230630-3.c` | 4 | 4 | 9 | i@0/24, c1@24/1, c2@25/1, c3@26/1, c4@27/1, c5@28/1, c6@29/1, c7@30/1, c8@31/1 |
| `20230630-4.c` | 4 | 4 | 9 | i@0/24, c1@24/1, c2@25/1, c3@26/1, c4@27/1, c5@28/1, c6@29/1, c7@30/1, c8@31/1 |
| `pr108498-2.c` | 44 | 4 | 5 | a@0/3, b@3/8, c@11/21, g@320/5, h@325/27 |
| `pr49123.c` | 4 | 4 | 1 | f@0/1 |
| `pr58984.c` | 4 | 4 | 3 | f0@0/8, <anonymous>@8/6, f1@14/5 |
| `pr65215-3.c` | 8 | 8 | 3 | l1@0/24, l2@24/8, l3@32/32 |
| `pr65215-4.c` | 8 | 8 | 1 | l1@0/48 |
| `pr70127.c` | 8 | 4 | 1 | g@32/2 |
| `pr89195.c` | 4 | 4 | 1 | i@0/24 |
| `pr97764.c` | 4 | 4 | 3 | b@0/3, c@3/28, d@31/1 |
