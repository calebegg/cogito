import { parse } from './parse.ts';
import { scan } from './scan.ts';
import { print } from './print.ts';
import { setSource } from './main.ts';

export function process(source: string) {
  setSource(source);
  try {
    return { status: 'success', data: print(parse(scan(source))) };
  } catch (e: unknown) {
    if (e instanceof Error) {
      return { status: 'error', data: e.toString() };
    } else {
      return { status: 'error', data: 'Unknown error' };
    }
  }
}
