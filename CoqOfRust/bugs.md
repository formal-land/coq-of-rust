# Bugs that Cannot Detected by coqc

### Order of Arguments

For traits their applications usually has the following form:

```
Sometrait.Trait Self a b c...
```

Sometimes I could mess up the order of the arguments, e.g. placing some wrong argument into the `Self`'s position and vice versa. I believe this needs further checks.

### Implicit / Explicit Arguments

When defining a trait, sometimes I could mess up whether an argument should be implicit or explicit. I believe this might cause potential bugs.