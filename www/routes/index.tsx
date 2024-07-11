/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { Try } from '../islands/Try.tsx';

const INTRO_SOURCE = outdent`
  function hello() {
    print("Hello, world!");
    return nil;
  }
`;

const FEATURES_SOURCE = outdent`
  function foo(x: number) {
    // You can define local variables
    y = x + 1;
    // And print things
    print("y is ~x0", y);
    // And assert things
    assert(y > x);
    // And return things
    return y;
  }

  theorem |foo works|(x: number) {
    return foo(x) > x;
  }

  function add-to-end(x: any, l: list) {
    return reduce(l, (acc, x) => cons(x, acc), [x]);
  }
  function rev(l: list) {
    if (is-empty(l)) {
      return [];
    } else {
      return add-to-end(first(l), rev(rest(l)));
    }
  }
  // This is actually kind of a cool theorem that ACL2 can prove by itself
  theorem |rev twice returns the original list|(l: list) {
    return rev(rev(l)) == l;
  }
`;

export default function Home() {
  return (
    <>
      <div class='main-header'>
        <h1>Cogito</h1>
      </div>
      <section>
        <p>
          Cogito is a small, simple, and expressive programming language that
          uses the{' '}
          <a href='https://www.cs.utexas.edu/~moore/acl2/'>
            ACL2 theorem prover
          </a>{' '}
          to execute functions and prove theorems. Try it out!
        </p>
        <Try initialSource={INTRO_SOURCE} />
      </section>
      <section>
        <div class='header'>
          <h2></h2>
        </div>
      </section>
      <section>
        <div class='header'>
          <h2>Features</h2>
        </div>
        <p>
          More info about features
        </p>
        <Try initialSource={FEATURES_SOURCE} />
      </section>
      <section>
        <div class='header'>
          <h2>Roadmap</h2>
        </div>
        <ul>
          <li>Counterexample generation</li>
          <li>More robust structs</li>
          <li>Pattern matching</li>
          <li>Reverse transpilation for error messages</li>
        </ul>
      </section>
      <section>
        <div class='header'>
          <h2>Credits</h2>
        </div>
        <ul>
          <li>
            <a href='https://ou.edu/content/dam/CoE/GraduatePrograms/Profiles/CS/Page,%20R%202011.pdf'>
              Rex Page
            </a>, my Master's thesis advisor and the professor who introduced me
            to ACL2
          </li>
          <li>
            <a href='https://craftinginterpreters.com/'>
              Crafting Interpreters by Robert Nystrom
            </a>, the basis of my parser and the inspiration for finally
            tackling this project after over a decade of rumination
          </li>
        </ul>
      </section>
    </>
  );
}
