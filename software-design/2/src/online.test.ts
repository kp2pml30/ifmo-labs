import {describe, expect, test} from '@jest/globals';
import {jest} from '@jest/globals';
import * as i from './index';

import { strict as assert } from 'node:assert';

test('online', async () => {
	let got = await i.getCommentsStats(i.defaultSock(), "btefjNXeaYg", 100)
	if (got instanceof Array) {
		expect(got.length).toEqual(100)
	} else {
		expect(got instanceof Array).toBeTruthy()
	}
})
