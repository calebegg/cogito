# Cogito (working title)

## How to read this document

- [I'm an ACL2 expert](#background-for-acl2-experts)
- [I'm an experienced developer](#more-details)
- [I'm a total novice, but I'm here to learn](#basic-introduction)

## Basic introduction

Cogito is a small, simple, and expressive programming language that uses the
[ACL2 theorem prover](https://www.cs.utexas.edu/~moore/acl2/) to execute
functions and prove theorems. Its familiar C-like syntax enforces the
constraints of ACL2 automatically.

Compared to writing raw ACL2, Cogito presents:

- A C-like syntax that's easy to learn and more familiar to most programmers
- A straightforward way to print debugging information
- The ability to easily define local variables without deep nesting
- TypeScript-style parameter types for functions and theorems that set up total
  functions and sane theorems without extra effort
- Global functions for common list operations like `map`, `flatMap`, `reduce`,
  `filter`, and `zipWith`

## More details

Cogito may superficially look like any other C-like language. But the extra
constraints that the syntax enforces actually allow code to be interpreted by
the sophisticated automatic ACL2 theorem prover, which can provide much more
confidence in your code compared to unit tests.

The intent of Cogito is to be a gentle way to access ACL2's power, specifically
through the lens of a teaching language for students unfamiliar with functional
programming languages. Through its syntax, Cogito provides basic **guard rails**
to make sure that the user is writing code that is more likely to succeed in
proof attempts without as much cognitive overhead.

## Examples

```c
function factorial(n: natural) {
  print("Factorializing ~x0", n);
  if (n == 0) {
    return 1;
  }
  return n * factorial(n - 1);
}

function add-to-end(xs: list, x: any) {
  if (empty(xs)) {
    return [x];
  } else {
    return concat([first(xs)], add-to-end(rest(xs), x));
  }
}
function rev(xs: list) {
  return reduce(xs as acc, x from []) {
    return add-to-end(acc, x)
  };
}
theorem |rev twice returns original list|(xs: list) {
  return rev(rev(xs)) == xs
}

// TODO: add measure
function merge(xs: list, ys: list) {
  if (empty(xs)) return ys;
  if (empty(ys)) return xs;
  if (first(xs) < first(ys)) {
    return [first(xs), ...merge(rest(xs), ys)];
  }
  return [first(ys), ...merge(xs, rest(ys))];
}

function foo() {
  x = 3;
  if (x < 5) {
    x = 4
  } else {
    x = 2
  }
  x = x + 3
  return x - 1
}

function sum(xs: list<number>) {
  return reduce(xs as acc, x from 0) {
    return acc + x;
  }
}
```
