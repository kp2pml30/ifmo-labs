import { strict as assert } from 'node:assert';

type EventBase = {id: number, time: Date}
type Event
	= {kind: "create_pass", base: EventBase, user_id: number}
	| {kind: "extend_pass", base: EventBase, user_id: number, to: Date}
	| {kind: "enter", base: EventBase, user_id: number, success: boolean}
	| {kind: "leave", base: EventBase, user_id: number}

	export type Week<T> = [T, T, T, T, T, T, T]

export type StoredUser = {user_id: number, to: Date | undefined, visits: Week<number>, lastUpdate: number}

export function emptyUser(user_id: number, event_id = -1): StoredUser {
	return {user_id, to: undefined, lastUpdate: event_id, visits: [0, 0, 0, 0, 0, 0, 0]}
}

export class Session {
	nextEventId: number = 0
	allEvents: Array<Event> = []
	addSubscribers = new Array<(user_id: number, event_id: number) => void>()

	private nextBase(): EventBase {
		return {id: this.nextEventId++, time: new Date()}
	}

	createUser(user_id: number) {
		if (this.allEvents.find((x) => x.kind == "create_pass" && x.user_id == user_id) !== undefined) {
			throw new Error(`duplciate user ${user_id}`)
		}
		const b = this.nextBase()
		this.allEvents.push({kind: "create_pass", base: b, user_id})
		for (const s of this.addSubscribers) {
			s(user_id, b.id)
		}
	}

	extendUserPass(user_id: number, to: Date) {
		if (this.allEvents.find((x) => x.kind == "create_pass" && x.user_id == user_id) === undefined) {
			throw new Error(`unknown user ${user_id}`)
		}
		this.allEvents.push({kind: "extend_pass", base: this.nextBase(), user_id, to})
	}

	updateUser(u: StoredUser): number {
		let events_count = 0
		//this.allEvents.sort((a, b) => {
		//	// compare times actually //if (a.base.time.getTime() != b.base.time.getTime())
		//	return b.base.id - a.base.id
		//})
		for (let i = u.lastUpdate + 1; i < this.allEvents.length; i++) {
			const e = this.allEvents[i];
			assert(e.base.id > u.lastUpdate)
			if (e.kind == "extend_pass" && e.user_id == u.user_id) {
				u.lastUpdate = e.base.id
				events_count++
				if (u.to === undefined || u.to < e.to) {
					u.to = e.to
				}
			} else if (e.kind == "enter" && e.user_id == u.user_id) {
				u.lastUpdate = e.base.id
				events_count++
				u.visits[e.base.time.getDay()] += +e.success
			}
		}
		return events_count
	}

	userStat(user_id: number): StoredUser {
		if (this.allEvents.find((x) => x.kind == "create_pass" && x.user_id == user_id) === undefined) {
			throw new Error(`unknown user ${user_id}`)
		}
		const r: StoredUser = emptyUser(user_id)
		this.updateUser(r)
		return r
	}

	userTryEnter(user_id: number): boolean {
		const now = new Date()
		const success = (this.allEvents.find((x) => x.kind == "extend_pass" && x.user_id == user_id && x.to >= now) !== undefined)
		this.allEvents.push({"kind": "enter", base: this.nextBase(), user_id, success})
		return success
	}

	userLeave(user_id: number) {
		// no check, because people sometimes leave not through main entrance
		this.allEvents.push({"kind": "leave", base: this.nextBase(), user_id})
	}

	getUsersIdsAndSubscribe(cb: (user_id: number, event_id: number) => void) {
		for (const u of this.allEvents) {
			if (u.kind == "create_pass") {
				cb(u.user_id, u.base.id)
			}
		}
		this.addSubscribers.push(cb)
	}
}

