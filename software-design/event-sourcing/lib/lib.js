"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.Session = exports.emptyUser = void 0;
const node_assert_1 = require("node:assert");
function emptyUser(user_id, event_id = -1) {
    return { user_id, to: undefined, lastUpdate: event_id, visits: [0, 0, 0, 0, 0, 0, 0] };
}
exports.emptyUser = emptyUser;
class Session {
    constructor() {
        this.nextEventId = 0;
        this.allEvents = [];
        this.addSubscribers = new Array();
    }
    nextBase() {
        return { id: this.nextEventId++, time: new Date() };
    }
    createUser(user_id) {
        if (this.allEvents.find((x) => x.kind == "create_pass" && x.user_id == user_id) !== undefined) {
            throw new Error(`duplciate user ${user_id}`);
        }
        const b = this.nextBase();
        this.allEvents.push({ kind: "create_pass", base: b, user_id });
        for (const s of this.addSubscribers) {
            s(user_id, b.id);
        }
    }
    extendUserPass(user_id, to) {
        if (this.allEvents.find((x) => x.kind == "create_pass" && x.user_id == user_id) === undefined) {
            throw new Error(`unknown user ${user_id}`);
        }
        this.allEvents.push({ kind: "extend_pass", base: this.nextBase(), user_id, to });
    }
    updateUser(u) {
        let events_count = 0;
        //this.allEvents.sort((a, b) => {
        //	// compare times actually //if (a.base.time.getTime() != b.base.time.getTime())
        //	return b.base.id - a.base.id
        //})
        for (let i = u.lastUpdate + 1; i < this.allEvents.length; i++) {
            const e = this.allEvents[i];
            (0, node_assert_1.strict)(e.base.id > u.lastUpdate);
            if (e.kind == "extend_pass" && e.user_id == u.user_id) {
                u.lastUpdate = e.base.id;
                events_count++;
                if (u.to === undefined || u.to < e.to) {
                    u.to = e.to;
                }
            }
            else if (e.kind == "enter" && e.user_id == u.user_id) {
                u.lastUpdate = e.base.id;
                events_count++;
                u.visits[e.base.time.getDay()] += +e.success;
            }
        }
        return events_count;
    }
    userStat(user_id) {
        if (this.allEvents.find((x) => x.kind == "create_pass" && x.user_id == user_id) === undefined) {
            throw new Error(`unknown user ${user_id}`);
        }
        const r = emptyUser(user_id);
        this.updateUser(r);
        return r;
    }
    userTryEnter(user_id) {
        const now = new Date();
        const success = (this.allEvents.find((x) => x.kind == "extend_pass" && x.user_id == user_id && x.to >= now) !== undefined);
        this.allEvents.push({ "kind": "enter", base: this.nextBase(), user_id, success });
        return success;
    }
    userLeave(user_id) {
        // no check, because people sometimes leave not through main entrance
        this.allEvents.push({ "kind": "leave", base: this.nextBase(), user_id });
    }
    getUsersIdsAndSubscribe(cb) {
        for (const u of this.allEvents) {
            if (u.kind == "create_pass") {
                cb(u.user_id, u.base.id);
            }
        }
        this.addSubscribers.push(cb);
    }
}
exports.Session = Session;
