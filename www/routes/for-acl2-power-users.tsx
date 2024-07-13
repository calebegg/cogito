/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

export default function ForAcl2PowerUsers() {
  return (
    <div style={{ maxWidth: 600, margin: 'auto' }}>
      <div class='main-header'>
        <h1>Cogito</h1>
      </div>
      <section>
        <div class='header'>
          <h2>For ACL2 power users</h2>
        </div>
        <h3>"Why not just write Lisp?"</h3>

        <p>
          I{' '}
          <strong>don't hate Lisp</strong>, and I definitely don't hate pure
          functional programming. But I still was motivated to create this
          alternative. I think there are a few solid reasons why an alternative
          is valuable.
        </p>

        <p>
          First of all, ACL2 has a fairly steep learning curve. Generally, I
          consider myself to have an intermediate knowledge of ACL2 after
          writing my undergraduate capstone with it, creating two separate
          iterations of Proof Pad
          (<a href='https://github.com/calebegg/proof-pad-classic'>1</a>,{' '}
          <a href='http://new.proofpad.org'>2</a>), writing{' '}
          <a href='https://github.com/calebegg/45-acl2-projects'>
            a collection of daily projects
          </a>, collecting and verifying{' '}
          <a href='http://hatrac.org'>84 theorems</a>{' '}
          from lectures and assignments, and implementing{' '}
          <a href='https://github.com/calebegg/proof-pad-classic/tree/master/dracula'>
            a pure ACL2 implementation of DrACuLa's utilities
          </a>, but I still struggle with the syntax and built-in function/macro
          naming. (Gun to my head, I couldn't tell you the difference between
          {' '}
          <code>princ$</code> and{' '}
          <code>prin1$</code>). ACL2 also has many curious omissions, like the
          lack of built-in <code>reduce</code>, <code>map</code>, and{' '}
          <code>filter</code>{' '}
          functions. Cogito aims to have a consistent, 'batteries-included'
          library of intuitive builtins.
        </p>

        <p>
          Secondly, for better or worse, Lisp is not a common language. It
          doesn't rank in{' '}
          <a href='https://www.tiobe.com/tiobe-index/'>
            the top 20 in the industry
          </a>. It's unlikely that undergraduate students will be familiar, and
          I feel that it's likely they'll spend more time trying to come to
          grips with Lisp than learning functional programming. (Sure, Cogito
          also doesn't rank in the top 20, of course. But it's heavily inspired
          by several languages that do; primarily C(++), Java, and JavaScript)
        </p>

        <p>
          Perhaps most importantly, I've come to believe that{' '}
          <strong>
            the simplicity of common lisp syntax and parsing
          </strong>{' '}
          is just shunting off complexity onto the programmer. Even adding basic
          {' '}
          <code>printf</code> style debugging (<code>cw</code>{' '}
          in ACL2) requires modifying the structure of your code, adding new
          parentheses in hard to predict ways, and probably ideally reindenting
          your code. In Cogito, it's as simple as adding a <code>print</code>
          {' '}
          statement on a new line.
        </p>

        <p>
          ACL2 has made great strides towards being a more expressive general
          purpose tool in the last few years, introducing loops and lambdas in
          recent versions. I think that's great, and I make use of both features
          in Cogito.
        </p>

        <h3>"What about the proof attempt output? It's still in lisp."</h3>

        <p>
          This is a peril with every transpiled language when it comes to
          runtime issues, but arguably worse in the world of ACL2 proof
          attempts. In general, my approach has always been that: a successful
          proof attempt is not worth reading, because you're done. An
          unsuccessful proof attempt is nearly always <em>also</em>{' '}
          not worth reading, because it's so hard to follow, even if you know
          ACL2 well.
        </p>

        <p>
          In the longer term, I'd like to use the type inputs to theorems to
          attempt counterexample production, and I'd also like to explore a
          reverse transformer from ACL2 output to Cogito like code, but it
          remains for now as a weakness in Cogito.
        </p>
      </section>
    </div>
  );
}
