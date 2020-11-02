/*!
 * CustomWiggle 3.4.3 cracked
 * https://greensock.com
 * 
 * @license Copyright 2020, GreenSock. All rights reserved.
 * Subject to the terms at https://greensock.com/standard-license or for Club GreenSock members, the agreement issued with that membership.
 * @author: Jack Doyle, jack@greensock.com
 */

!
function(n, e) {
    "object" == typeof exports && "undefined" != typeof module ? e(exports) : "function" == typeof define && define.amd ? define(["exports"], e) : e((n = n || self).window = n.window || {})
} (this,
function(e) {
    "use strict";
    function g() {
        return t || "undefined" != typeof window && (t = window.gsap) && t.registerPlugin && t
    }
    function i(n) {
        return n
    }
    function j(n) {
        if (!C) if (t = g(), y = t && t.parseEase("_CE")) {
            for (var e in M) M[e] = y("", M[e]);
            C = 1,
            o("wiggle").config = function(n) {
                return "object" == typeof n ? o("", n) : o("wiggle(" + n + ")", {
                    wiggles: +n
                })
            }
        } else n && console.warn("Please gsap.registerPlugin(CustomEase, CustomWiggle)")
    }
    function k(e, n) {
        return "function" != typeof e && (e = t.parseEase(e) || y("", e)),
        e.custom || !n ? e: function(n) {
            return 1 - e(n)
        }
    }
    var t, C, y, M = {
        easeOut: "M0,1,C0.7,1,0.6,0,1,0",
        easeInOut: "M0,0,C0.1,0,0.24,1,0.444,1,0.644,1,0.6,0,1,0",
        anticipate: "M0,0,C0,0.222,0.024,0.386,0,0.4,0.18,0.455,0.65,0.646,0.7,0.67,0.9,0.76,1,0.846,1,1",
        uniform: "M0,0,C0,0.95,0,1,0,1,0,1,1,1,1,1,1,1,1,0,1,0"
    },
    r = "CustomWiggle",
    O = true,
    o = function _create(n, e) {
        C || j(1);
        var t, o, r, u, s, a, f, g, l, c = 0 | ((e = e || {}).wiggles || 10),
        d = 1 / c,
        p = d / 2,
        w = "anticipate" === e.type,
        h = M[e.type] || M.easeOut,
        m = i;
        if (O) {
            if (w && (m = h, h = M.easeOut), e.timingEase && (m = k(e.timingEase)), e.amplitudeEase && (h = k(e.amplitudeEase, !0)), g = [0, 0, (a = m(p)) / 4, 0, a / 2, f = w ? -h(p) : h(p), a, f], "random" === e.type) {
                for (g.length = 4, t = m(d), o = 2 * Math.random() - 1, l = 2; l < c; l++) p = t,
                f = o,
                t = m(d * l),
                o = 2 * Math.random() - 1,
                r = Math.atan2(o - g[g.length - 3], t - g[g.length - 4]),
                u = Math.cos(r) * d,
                s = Math.sin(r) * d,
                g.push(p - u, f - s, p, f, p + u, f + s);
                g.push(t, 0, 1, 0)
            } else {
                for (l = 1; l < c; l++) g.push(m(p + d / 2), f),
                p += d,
                f = (0 < f ? -1 : 1) * h(l * d),
                a = m(p),
                g.push(m(p - d / 2), f, a, f);
                g.push(m(p + d / 4), f, m(p + d / 4), 0, 1, 0)
            }
            for (l = g.length; - 1 < --l;) g[l] = ~~ (1e3 * g[l]) / 1e3;
            return g[2] = "C" + g[2],
            y(n, "M" + g.join(","))
        }
    },
    s = (CustomWiggle.create = function create(n, e) {
        return o(n, e)
    },
    CustomWiggle.register = function register(n) {
        t = n,
        j()
    },
    CustomWiggle);
    function CustomWiggle(n, e) {
        this.ease = o(n, e)
    }
    g() && t.registerPlugin(s),
    s.version = "3.4.3",
    e.CustomWiggle = s,
    e.
default = s;
    if (typeof(window) === "undefined" || window !== e) {
        Object.defineProperty(e, "__esModule", {
            value: !0
        })
    } else {
        delete e.
    default
    }
});
