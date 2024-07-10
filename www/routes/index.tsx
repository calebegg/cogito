import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { Try } from '../islands/Try.tsx';

const INITIAL_SOURCE = outdent`
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
      <h1>Cogito</h1>
      Hello Kenny, this is just for you, I will put some more explanatory text
      here later.
      <Try initialSource={INITIAL_SOURCE} />
    </>
  );
}
