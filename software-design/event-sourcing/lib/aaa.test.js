"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
Object.defineProperty(exports, "__esModule", { value: true });
const globals_1 = require("@jest/globals");
const globals_2 = require("@jest/globals");
const i = __importStar(require("./lib"));
globals_2.jest
    .useFakeTimers();
function addDays(d, ds) {
    const copy = new Date(d);
    copy.setDate(d.getDate() + ds);
    return copy;
}
(0, globals_1.test)('session', () => {
    const session = new i.Session();
    const fakeNow = new Date('2020-01-01');
    globals_2.jest.setSystemTime(fakeNow);
    (0, globals_1.expect)(() => session.extendUserPass(1, new Date())).toThrow();
    session.createUser(1);
    (0, globals_1.expect)(() => session.createUser(1)).toThrow();
    session.createUser(2);
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(false);
    session.extendUserPass(1, addDays(fakeNow, 2));
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(true);
    (0, globals_1.expect)(session.userTryEnter(2)).toEqual(false);
    globals_2.jest.setSystemTime(addDays(fakeNow, 3));
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(false);
    globals_2.jest.setSystemTime(addDays(fakeNow, 3));
    session.extendUserPass(1, addDays(fakeNow, 4));
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(true);
});
(0, globals_1.test)('incremental', () => {
    const session = new i.Session();
    const fakeNow = new Date('2020-01-01');
    globals_2.jest.setSystemTime(fakeNow);
    let user;
    session.getUsersIdsAndSubscribe((user_id, event_id) => {
        (0, globals_1.expect)(user).toBeUndefined();
        user = i.emptyUser(user_id, event_id);
    });
    (0, globals_1.expect)(user).toBeUndefined();
    session.createUser(1);
    (0, globals_1.expect)(user).not.toBeUndefined();
    const user1 = user;
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(false);
    session.extendUserPass(1, addDays(fakeNow, 2));
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(true);
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(true);
    (0, globals_1.expect)(session.updateUser(user1)).toEqual(4);
    (0, globals_1.expect)(user1.to).toEqual(addDays(fakeNow, 2));
    const exp = [0, 0, 0, 0, 0, 0, 0];
    exp[fakeNow.getDay()] += 2;
    (0, globals_1.expect)(user1.visits).toEqual(exp);
    globals_2.jest.setSystemTime(addDays(fakeNow, 1));
    (0, globals_1.expect)(session.userTryEnter(1)).toEqual(true);
    (0, globals_1.expect)(session.updateUser(user1)).toEqual(1);
    exp[(fakeNow.getDay() + 1) % 7] += 1;
    (0, globals_1.expect)(user1.visits).toEqual(exp);
});
