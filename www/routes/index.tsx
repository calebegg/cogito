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

  theorem |foo increases|(x: number) {
    return foo(x) > x;
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
        <ul>
          <li>
            <b>Easy to Learn, Powerful to Use:</b>{' '}
            Familiar syntax and concepts for beginners, while offering advanced
            features like theorems and functional programming for experienced
            developers.
          </li>
          <li>
            <b>Prove Your Code Works:</b>{' '}
            Go beyond testing by formally proving the correctness of your
            functions, ensuring your programs behave exactly as intended.
          </li>
          <li>
            <b>Built-in Formal Methods:</b>{' '}
            Leverage the power of ACL2, a renowned tool for rigorous software
            verification, without needing to learn its complex syntax.
          </li>
          <li>
            <b>Concise and Readable:</b>{' '}
            Write clear, expressive code using intuitive structures like struct
            for data and types for safety.
          </li>
          <li>
            <b>Functional Programming Made Accessible:</b>{' '}
            Explore a different style of programming based on functions and
            recursion, unlocking new problem-solving approaches.
          </li>
          <li>
            <b>Bridge to Advanced Concepts:</b>{' '}
            A stepping stone to understanding formal verification, functional
            programming, and the ACL2 ecosystem.
          </li>
        </ul>
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
          <h2>Resources</h2>
        </div>
        <ul>
          <li>
            <a href='https://github.com/calebegg/cogito'>
              File issues and send PRs on Github
            </a>
          </li>
          <li>
            <a href='./style-guide'>
              Style guide (coming soon!)
            </a>
          </li>
          <li>
            <a href='./for-acl2-power-users'>
              Some thoughts for ACL2 power users
            </a>
          </li>
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
