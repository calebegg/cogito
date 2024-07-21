/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import { useEffect, useState } from 'preact/hooks';
import { process } from '../../src/index.ts';
import { CodeMirror } from '../components/CodeMirror.tsx';
import {
  CircleCheck,
  CircleDot,
  CircleX,
  LoaderCircle,
} from 'https://esm.sh/lucide-preact@0.408.0';

enum Tab {
  LISP,
  ACL2_SUMMARY,
  RAW_ACL2,
}

export function Try({ initialSource }: { initialSource: string }) {
  const [output, setOutput] = useState<string[]>([]);
  const [lisp, setLisp] = useState('');
  const [currentTab, setCurrentTab] = useState(Tab.ACL2_SUMMARY);
  const [source, setSource] = useState(initialSource);
  const [error, setError] = useState(false);

  useEffect(() => {
    setError(false);
    const lispSource = process(source);
    let timeoutId: number | null = null;
    let ws: WebSocket | null = null;
    setLisp(lispSource.data);
    if (lispSource.status === 'error') {
      setError(true);
      setOutput(['Parse error']);
    } else {
      setOutput([]);
      timeoutId = setTimeout(() => {
        ws = new WebSocket(
          `wss://acl2-jbhe53iwqa-uc.a.run.app/acl2?preamble=(set-verify-guards-eagerness 0)`,
        );
        ws.addEventListener('message', ({ data }) => {
          setOutput((o) => [...o, data]);
        });
        ws.addEventListener('error', () => {
          setOutput((o) => [...o, 'Unexpected socket error']);
        });
        if (ws.readyState === WebSocket.CONNECTING) {
          ws.addEventListener('open', () => {
            ws!.send('(set-guard-checking :nowarn) ' + lispSource.data);
          });
        } else {
          ws.send('(set-guard-checking :nowarn) ' + lispSource.data);
        }
        timeoutId = null;
      }, source == initialSource ? 0 : 2500);
    }
    return () => {
      if (timeoutId) clearTimeout(timeoutId);
      if (ws && ws.readyState === WebSocket.OPEN) ws.close();
      setOutput([]);
    };
  }, [source]);

  return (
    <div class='row-on-wide'>
      <div style={{ paddingTop: 36, flex: 1 }}>
        <CodeMirror
          initialValue={initialSource}
          onChange={(v) => setSource(v)}
        />
      </div>
      <div style={{ flex: '1' }}>
        <div style='display: flex' role='tablist'>
          <button
            role='tab'
            class={'tab ' + (currentTab === Tab.LISP ? 'current' : '')}
            onClick={() => setCurrentTab(Tab.LISP)}
          >
            Lisp source code
          </button>
          <button
            role='tab'
            class={'tab ' + (currentTab === Tab.ACL2_SUMMARY ? 'current' : '')}
            onClick={() => setCurrentTab(Tab.ACL2_SUMMARY)}
          >
            ACL2 summary
          </button>
          <button
            role='tab'
            class={'tab ' + (currentTab === Tab.RAW_ACL2 ? 'current' : '')}
            onClick={() => setCurrentTab(Tab.RAW_ACL2)}
          >
            Raw ACL2 output
          </button>
        </div>
        {currentTab === Tab.LISP
          ? (
            <pre
              style={{ whiteSpace: 'pre-wrap' }}
              role='tabpanel'
              class={error ? 'error' : ''}
            >{lisp}</pre>
          )
          : currentTab === Tab.ACL2_SUMMARY
          ? (
            <div
              role='tabpanel'
              style={{
                display: 'flex',
                flexDirection: 'column',
                gap: 16,
                padding: 16,
                border: 'solid #888 1px',
              }}
            >
              {output.length === 0
                ? (
                  <div
                    style={{
                      display: 'flex',
                      justifyContent: 'center',
                      paddingTop: 32,
                      paddingBottom: 32,
                    }}
                  >
                    <LoaderCircle />
                  </div>
                )
                : output.map((o) => summarize(o)).filter((s): s is Summary =>
                  s != null
                ).map(
                  (s) => (
                    <div>
                      {s.state === 'success'
                        ? (
                          <CircleCheck
                            color='green'
                            style={{ verticalAlign: -6, marginRight: 16 }}
                          />
                        )
                        : s.state === 'text'
                        ? (
                          <CircleDot
                            color='#888'
                            style={{ verticalAlign: -6, marginRight: 16 }}
                          />
                        )
                        : (
                          <CircleX
                            color='red'
                            style={{ verticalAlign: -6, marginRight: 16 }}
                          />
                        )}
                      {s.message}
                    </div>
                  ),
                )}
            </div>
          )
          : (
            <div role='tabpanel' style={{ overflow: 'auto', maxHeight: 400 }}>
              {output.filter((o) => o.length > 0).map((o) => (
                <>
                  <pre>{o}</pre>
                  <hr />
                </>
              ))}
            </div>
          )}
      </div>
    </div>
  );
}

interface Summary {
  state: 'success' | 'failure' | 'text';
  message: string;
}

function summarize(output: string): Summary | null {
  if (!output) return null;
  if (output === 'Leaving guard checking on, but changing value to :NOWARN.') {
    return null;
  }
  const state: Summary['state'] = [
      '************ ABORTING from raw Lisp ***********',
      '******** FAILED ********',
      'HARD ACL2 ERROR',
      'ACL2 Error',
      'Parse error',
    ].some((m) => output.includes(m))
    ? 'failure'
    : 'success';

  if (output.includes('APPLY$-WARRANT-COGITO-')) return null;
  const summaryMatch = output.match(
    new RegExp(`Summary
Form:\\s+\\( ([A-Z:-]+) (.*) \\.\\.\\.\\)`),
  );
  const structMatch = output.match(/\(STD::DEFAGGREGATE ([A-Z:-]+)\)$/);
  if (!summaryMatch) {
    return {
      state: state === 'success' ? 'text' : state,
      message: output.substring(0, 80) + (output.length > 80 ? '...' : ''),
    };
  } else if (
    summaryMatch[2].startsWith('COGITO-')
  ) {
    return null;
  } else if (summaryMatch[1] === 'INCLUDE-BOOK') {
    return { state, message: 'Importing ${summaryMatch[2]}' };
  } else if (summaryMatch[1] === 'DEFUN') {
    return { state, message: `Admission of ${summaryMatch[2]}` };
  } else if (summaryMatch[1] === 'DEFTHM') {
    return { state, message: `Proof of ${summaryMatch[2]}` };
  } else if (summaryMatch[1] === 'MUTUAL-RECURSION') {
    return { state, message: `Admission of mutually recursive functions` };
  } else if (summaryMatch[1] === 'DEFCONST') {
    return { state, message: `Declaration of const ${summaryMatch[2]}` };
  } else if (structMatch) {
    return { state, message: `Generating struct ${structMatch[1]}` };
  } else if (output.includes('Assertion failed')) {
    return { state, message: 'Assertion failed' };
  }
  return { state, message: 'Unknown response' };
}
