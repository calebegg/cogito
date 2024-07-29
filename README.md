# [Cogito](https://cogitolang.org)

Cogito is a small, simple, and expressive programming language that
uses the [ACL2 theorem prover](https://www.cs.utexas.edu/~moore/acl2/)
to execute functions and prove theorems.

## Getting Started

The easiest way to get started with Cogito is to visit [the
website](https://cogitolang.org), which provides a playground in which
you can write and run Cogito programs.

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

## Development

Cogito runs on top of [Deno](https://deno.com/). To build and run the
website locally, install [Deno](https://deno.com/) and then run the
following command in the top-level directory of this repo:

```bash
deno task www
```

This will install any needed dependencies and set up a development
server, typically at `localhost:8000`. The URL that the site is being
served at will be printed to the terminal, so navigate there in your
browser to play around with the site!

Note that even a local version of the Cogito website will use a
predeployed ACL2 backend when evaluating ACL2 forms. The source for
the backend is provided in the [Proof Pad
repo](https://github.com/calebegg/proof-pad), but more complete
documentation on deploying the ACL2 backend and configuring the Cogito
website to use it is a work in progress.
