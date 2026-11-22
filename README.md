# Mini Separation Logic

A minimal model of an impure language with memory, mutation and nondeterminism
along with a separation logic to write specs about programs, made to be minimal
an educational.

## What is Separation Logic (SL) ?

SL is one of the fundamental ideas that allows formal verification to
go from only verifying idealized pure functional code to "real" code that
mutates memory and has non-determinism.

SL is a program logic allowing us to **expressively** write specifications about
**impure** functions in a composable way, such that you can easily compose the
spec of individual functions into a spec of a function that uses said functions.

