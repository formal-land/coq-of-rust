# Bugs that Cannot Detected by coqc

### Order of Arguments

For traits their applications usually has the following form:

```
Sometrait.Trait Self a b c...
```

Sometimes I could mess up the order of the arguments, e.g. placing some wrong argument into the `Self`'s position and vice versa. I believe this needs further checks.

### Implicit / Explicit Arguments

When defining a trait, sometimes I could mess up whether an argument should be implicit or explicit. I believe this might cause potential bugs.

### Types in Traits

Say, we have two traits A and B, where B is a trait of A. If we have defined `type Output;` in trait A, then it looks like we're supposed to also to be able to use this `Output` in trait B. Currently, we'll define an extra parameter `Output` in B to resolve this problem.

This can have a variant, defining consts in traits, which appears in the `simd` module.