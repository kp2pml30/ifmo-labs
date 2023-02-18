import {describe, expect, test} from '@jest/globals';

import {jest} from '@jest/globals';
import * as i from './lib';

import { strict as assert } from 'node:assert';

jest
	.useFakeTimers()

function addDays(d: Date, ds: number) {
	const copy = new Date(d);
	copy.setDate(d.getDate() + ds)
	return copy
}

test('session', () => {
	const session = new i.Session()

	const fakeNow = new Date('2020-01-01')
	jest.setSystemTime(fakeNow)

	expect(() => session.extendUserPass(1, new Date())).toThrow()
	session.createUser(1)
	expect(() => session.createUser(1)).toThrow()
	session.createUser(2)

	expect(session.userTryEnter(1)).toEqual(false)
	session.extendUserPass(1, addDays(fakeNow, 2))
	expect(session.userTryEnter(1)).toEqual(true)
	expect(session.userTryEnter(2)).toEqual(false)
	jest.setSystemTime(addDays(fakeNow, 3))
	expect(session.userTryEnter(1)).toEqual(false)

	jest.setSystemTime(addDays(fakeNow, 3))
	session.extendUserPass(1, addDays(fakeNow, 4))
	expect(session.userTryEnter(1)).toEqual(true)
})

test('incremental', () => {
	const session = new i.Session()

	const fakeNow = new Date('2020-01-01')
	jest.setSystemTime(fakeNow)

	let user: i.StoredUser | undefined

	session.getUsersIdsAndSubscribe((user_id, event_id) => {
		expect(user).toBeUndefined()
		user = i.emptyUser(user_id, event_id)
	})

	expect(user).toBeUndefined()

	session.createUser(1)
	expect(user).not.toBeUndefined()
	const user1 = user!
	expect(session.userTryEnter(1)).toEqual(false)
	session.extendUserPass(1, addDays(fakeNow, 2))
	expect(session.userTryEnter(1)).toEqual(true)
	expect(session.userTryEnter(1)).toEqual(true)

	expect(session.updateUser(user1)).toEqual(4)
	expect(user1.to).toEqual(addDays(fakeNow, 2))
	const exp = [0, 0, 0, 0, 0, 0, 0]
	exp[fakeNow.getDay()] += 2
	expect(user1.visits).toEqual(exp)

	jest.setSystemTime(addDays(fakeNow, 1))
	expect(session.userTryEnter(1)).toEqual(true)
	expect(session.updateUser(user1)).toEqual(1)
	exp[(fakeNow.getDay() + 1) % 7] += 1
	expect(user1.visits).toEqual(exp)
})
