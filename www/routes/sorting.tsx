import outdent from 'https://deno.land/x/outdent@v0.8.0/mod.ts';
import { Try } from '../islands/Try.tsx';

export default function Sorting() {
  return (
    <>
      <div class='main-header'>
        <h1>Cogito</h1>
      </div>
      <p>
        These examples are a work in progress and not all of them admit
        currently.
      </p>
      <section>
        <h2>Insertion sort</h2>
        <Try
          initialSource={outdent`
            function insert(x: number, xs: list<number>) {
              if (is-empty(xs)) {
                return [x];
              }
              if (first(xs) > x) {
                return [x, first(xs), ...rest(xs)];
              }
              return [first(xs), ...insert(x, rest(xs))];
            }
            
            
            theorem |insert preserves length|(x: number, list: list<number>) {
              return len(insert(x, list)) == len(list) + 1;
            }
            
            function is-ordered(xs: list<number>) {
              if (is-empty(xs) || len(xs) == 1) {
                return true;
              } else {
                return first(xs) <= second(xs) && is-ordered(rest(xs));
              }
            }
            
            function isort(xs: list<number>) {
              if (is-empty(rest(xs))) {
                return xs;
              }
              return insert(first(xs), isort(rest(xs)));
            }
            
            theorem |isort sorts|(list: list<number>) {
              return is-ordered(isort(list));
            }
            
            const *jenny* = [8, 6, 7, 5, 3, 0, 9];
            
            main {
              print("~x0", isort(*jenny*));
              print("~x0", is-ordered(isort(*jenny*)));
            }
          `}
        />
      </section>
      <section>
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
              if (len(xs) <= 1) {
                return (xs, []);
              }
              (ys, zs) = dmx(rest(xs));
              return ([first(xs), ...zs], ys);
            }
            
            theorem dmx-shortens(xs: list) {
              (ys, zs) = dmx(xs);
              return len(xs) > 1 ->
                len(ys) < len(xs) && len(zs) < len(xs);
            }
            
            function msort(xs: list<number>) {
              if (len(xs) <= 1) {
                return xs;
              }
              (ys, zs) = dmx(xs);
              return mrg(msort(ys), msort(zs));
            }
            
            const *jenny* = [8, 6, 7, 5, 3, 0, 9];
            
            main {
              print("~x0", msort(*jenny*));
            }
          `}
        />
      </section>
      <section>
        <h2>Quick sort</h2>
        <Try
          initialSource={outdent`
            function partition(list: list<number>, pivot: number) {
              if (is-empty(list)) {
                return ([], []);
              }
              (less, greater) = partition(rest(list), pivot);
              if (first(list) < pivot) {
                return ([first(list), ...less], greater);
              } else {
                return (less, [first(list), ...greater]);
              }
            }

            theorem |partition preserves length|(list: list<number>, pivot: number) {
              (less, greater) = partition(list, pivot);
              return len(less) + len(greater) == len(list);
            }

            function qsort(list: list<number>) {
              if (is-empty(list)) {
                return [];
              }
              pivot = first(list);
              (less, greater) = partition(rest(list), pivot);
              return [...qsort(less), pivot, ...qsort(greater)];
            }

            theorem |qsort preserves length|(list: list<number>) {
              return len(list) == len(qsort(list));
            }

            const *jenny* = [8, 6, 7, 5, 3, 0, 9];

            main {
              print("~x0", qsort(*jenny*));
            }
          `}
        />
      </section>
    </>
  );
}
