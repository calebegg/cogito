# Cogito (working title)

```c
function is-palindrome(l: list) {
  reversed = reverse(l);
  print("Original list: ~x0", l);
  print("Reversed list: ~x0", reversed);
  return l == reversed;
}

theorem |is-palindrome is equivalent on a reversal|(l: list) {
  return is-palindrome(reverse(l)) == is-palindrome(l);
}
theorem |is-palindrome works on even palindromes|(l: list) {
  return is-palindrome([...l, ...reverse(l)]);
}
theorem |is-palindrome works on odd palindromes|(l: list, x: any) {
  return is-palindrome([...l, x, ...reverse(l)]);
}
```

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

## Background for ACL2 experts

### Why not just write ACL2?

I consider myself to have an intermediate knowledge of ACL2 after writing my
undergraduate capstone with it and creating two separate iterations of
[Proof Pad](http://new.proofpad.org), but I struggle with even basic macros and
find myself bewildered by how to coherently structure even simple programs. For
better or worse, I've always wanted a C-like syntax. I think many students early
in learning programming would also benefit from this approach.

Essentially, I've come to believe that **the simplicity of common lisp syntax
and parsing** is just shunting off complexity onto the programmer. Even adding
basic `printf` style debugging (`cw` in ACL2) requires modifying the structure
of your code. In Cogito, it's as simple as adding a `print` statement on a new
line.

### What about the proof attempt output? It's still in lisp

This is a peril with every transpiled language when it comes to runtime issues,
but arguably worse in the world of ACL2 proof attempts. In general, my approach
has always been that: a successful proof attempt is not worth reading, because
you're done. An unsuccessful proof attempt is nearly always _also_ not worth
reading, because it's so hard to follow, even if you know ACL2 well.

In the longer term, I'd like to use the type inputs to theorems to attempt
counterexample production, and I'd also like to explore a reverse transformer
from ACL2 output to Cogito like code, but it remains for now as a weakness in
Cogito.

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
