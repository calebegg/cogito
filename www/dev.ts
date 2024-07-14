#!/usr/bin/env -S deno run -A --watch=static/,routes/
/**
 * @license
 * Copyright 2024 Google LLC
 * SPDX-License-Identifier: Apache-2.0
 */

import dev from '$fresh/dev.ts';
import config from './fresh.config.ts';

import '$std/dotenv/load.ts';

await dev(import.meta.url, './main.ts', config);
