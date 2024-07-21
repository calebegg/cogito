import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { Try } from '../islands/Try.tsx';

export default function Advanced() {
  return (
    <>
      <div class='main-header'>
        <h1>Cogito</h1>
      </div>
      <h2>Merge sort</h2>
      <Try
        initialSource={outdent`
          function mrg(xs: list<number>, ys: list<number>) {
            measure(len(xs) + len(ys));
            if (is-empty(xs)) { return ys; }
            if (is-empty(ys)) { return xs; }
            x = first(xs);
            y = first(ys);
            if (x < y) {
              return [x, ...mrg(rest(xs), ys)];
            }
            return [y, ...mrg(xs, rest(ys))];
          }

          function dmx(xs: list) {
            if (is-empty(xs)) {
              return ([], []);
            }
            (ys, zs) = dmx(rest(xs));
            return ([first(xs), ...zs], ys);
          }
        `}
      />
    </>
  );
}
