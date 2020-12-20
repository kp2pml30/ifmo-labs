// ==UserScript==
// @name         Pcms time
// @namespace    myscripts
// @version      0.1
// @description  fancy pcms time
// @author       kp2pml30
// @match        http://neerc.ifmo.ru/pcms2client/*
// @grant        none
// ==/UserScript==

(function() {
    'use strict';
    var el = document.getElementById("running-clock")
    if (el === null) {
        el = document.getElementById("submit:running-clock")
    }

    function trySimpleReplace() {
        var el = document.getElementsByClassName("standings")
        if (el.length > 1) {
            el = el[0]
        } else {
            return
        }
        until1 = el.innerHTML.match(/([0-9]+):([0-9]+) из ([0-9]+):([0-9]+)/)
        from  = new Date().getTime() - (Number.parseInt(until1[1]) * 60 + Number.parseInt(until1[2])) * 1000
        if (until1 === null || until1.length < 4) {
            return
        }
        until = from + (Number.parseInt(until1[3]) * 60 + Number.parseInt(until1[4])) * 1000

        var now = new Date().getTime()
        if (now < until) {
            el.innerHTML = el.innerHTML.replace(until1[0], formatTime(now) + " из " + formatTime(until))
        }
    }

    if (el === null) {
        trySimpleReplace()
        return
    }
    var until1 = el.textContent.match(/([0-9]+):([0-9]+) из ([0-9]+):([0-9]+)/)
    var from  = new Date().getTime() - (Number.parseInt(until1[1]) * 60 + Number.parseInt(until1[2])) * 1000

    function formatTime(t) {
        t -= from
        t /= 1000
        var ret = ""
        var days = Math.floor(t / 60 / 60 / 24)
        if (days > 0) {
            ret += days.toString() + ":"
        }
        var hours = Math.floor(t / 60 / 60 % 24)
        if (hours > 9) {
            ret += hours.toString() + ":"
        } else if (hours != 0) {
            ret += "0" + hours.toString() + ":"
        }
        var mins = Math.floor(t / 60 % 60)
        if (mins > 9) {
            ret += mins.toString() + ":"
        } else {
            ret += "0" + mins.toString() + ":"
        }
        var secs = Math.floor(t % 60)
        if (secs > 9) {
            ret += secs.toString()
        } else {
            ret += "0" + secs.toString()
        }
        return ret
    }

    var until = from + (Number.parseInt(until1[3]) * 60 + Number.parseInt(until1[4])) * 1000
    var patchedFrom = null
    function myTimer() {
        var now = new Date().getTime()
        if (now < until) {
            el.textContent = formatTime(now) + " из " + formatTime(until)
            setTimeout(myTimer, 1000)
        } else {
            el.textContent = "END"
        }
    }
    var oldTimeout = window.setTimeout
    window.setTimeout = function(callback, timeout) {
        if (callback == patchedFrom) {
            oldTimeout(myTimer, timeout)
        } else {
            var checker = function() {
                var before = el.innerHTML
                callback.apply(null, arguments)
                if (el.innerHTML !== before) {
                    patchedFrom = callback
                }
            }
            oldTimeout(checker, timeout)
        }
    }
})();