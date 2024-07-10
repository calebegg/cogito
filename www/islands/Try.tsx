import { useEffect, useState } from 'preact/hooks';
import { process } from '../../src/index.ts';

const ws = new WebSocket(`wss://acl2-jbhe53iwqa-uc.a.run.app/acl2`);

export interface Acl2Response {
  Kind: string;
  Body: string;
}

export function Try({ initialSource }: { initialSource: string }) {
  const [output, setOutput] = useState('');
  const [source, setSource] = useState(initialSource);
  const [error, setError] = useState(false);

  useEffect(() => {
    setError(false);
    const acl2Source = process(source);
    let id = -1;
    if (acl2Source.status === 'error') {
      setError(true);
      setOutput(acl2Source.data);
    } else {
      setOutput(acl2Source.data);
      // setOutput('Loading...');
      // id = setTimeout(() => {
      //   ws.addEventListener('message', (e) => {
      //     const data = JSON.parse(e.data) as Acl2Response;
      //     setError(data.Kind === 'ERROR');
      //     setOutput(data.Body);
      //   }, { once: true });
      //   ws.send(acl2Source.data);
      // }, 1000);
    }
    return () => {
      clearTimeout(id);
      setOutput('');
    };
  }, [source]);

  return (
    <div style='display: flex; gap: 16px;'>
      <textarea
        rows={40}
        cols={80}
        value={source}
        onInput={(e) => {
          setSource((e.target as HTMLTextAreaElement).value);
        }}
      />
      <div>
        <p style={{ maxWidth: 400 }}>
          Eventually this will show the output from ACL2 itself, not just the
          source code, but that's broken for complex reasons right now. You can
          copy and paste it into <a href='http://new.proofpad.org'>Proof Pad</a>
          {' '}
          if you want. Also it's not formatted right because formatting
          is hard.
        </p>
        <textarea
          readonly
          rows={40}
          cols={80}
          value={output}
          style={{ background: error ? 'lightred' : 'white' }}
        />
      </div>
    </div>
  );
}
