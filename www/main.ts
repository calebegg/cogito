/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

/// <reference no-default-lib="true" />
/// <reference lib="dom" />
/// <reference lib="dom.iterable" />
/// <reference lib="dom.asynciterable" />
/// <reference lib="deno.ns" />

import '$std/dotenv/load.ts';

import { start } from 'https://deno.land/x/fresh@1.6.8/server.ts';
import manifest from './fresh.gen.ts';
import config from './fresh.config.ts';

await start(manifest, config);
