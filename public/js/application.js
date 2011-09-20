// Copyright (c) 2005  Tom Wu
// All Rights Reserved.
// See "LICENSE" for details.

// Basic JavaScript BN library - subset useful for RSA encryption.

// Bits per digit
var dbits;

// JavaScript engine analysis
var canary = 0xdeadbeefcafe;
var j_lm = ((canary&0xffffff)==0xefcafe);

// (public) Constructor
function BigInteger(a,b,c) {
  if(a != null)
    if("number" == typeof a) this.fromNumber(a,b,c);
    else if(b == null && "string" != typeof a) this.fromString(a,256);
    else this.fromString(a,b);
}

// return new, unset BigInteger
function nbi() { return new BigInteger(null); }

// am: Compute w_j += (x*this_i), propagate carries,
// c is initial carry, returns final carry.
// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
// We need to select the fastest one that works in this environment.

// am1: use a single mult and divide to get the high bits,
// max digit bits should be 26 because
// max internal value = 2*dvalue^2-2*dvalue (< 2^53)
function am1(i,x,w,j,c,n) {
  while(--n >= 0) {
    var v = x*this[i++]+w[j]+c;
    c = Math.floor(v/0x4000000);
    w[j++] = v&0x3ffffff;
  }
  return c;
}
// am2 avoids a big mult-and-extract completely.
// Max digit bits should be <= 30 because we do bitwise ops
// on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
function am2(i,x,w,j,c,n) {
  var xl = x&0x7fff, xh = x>>15;
  while(--n >= 0) {
    var l = this[i]&0x7fff;
    var h = this[i++]>>15;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x7fff)<<15)+w[j]+(c&0x3fffffff);
    c = (l>>>30)+(m>>>15)+xh*h+(c>>>30);
    w[j++] = l&0x3fffffff;
  }
  return c;
}
// Alternately, set max digit bits to 28 since some
// browsers slow down when dealing with 32-bit numbers.
function am3(i,x,w,j,c,n) {
  var xl = x&0x3fff, xh = x>>14;
  while(--n >= 0) {
    var l = this[i]&0x3fff;
    var h = this[i++]>>14;
    var m = xh*l+h*xl;
    l = xl*l+((m&0x3fff)<<14)+w[j]+c;
    c = (l>>28)+(m>>14)+xh*h;
    w[j++] = l&0xfffffff;
  }
  return c;
}
if(j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
  BigInteger.prototype.am = am2;
  dbits = 30;
}
else if(j_lm && (navigator.appName != "Netscape")) {
  BigInteger.prototype.am = am1;
  dbits = 26;
}
else { // Mozilla/Netscape seems to prefer am3
  BigInteger.prototype.am = am3;
  dbits = 28;
}

BigInteger.prototype.DB = dbits;
BigInteger.prototype.DM = ((1<<dbits)-1);
BigInteger.prototype.DV = (1<<dbits);

var BI_FP = 52;
BigInteger.prototype.FV = Math.pow(2,BI_FP);
BigInteger.prototype.F1 = BI_FP-dbits;
BigInteger.prototype.F2 = 2*dbits-BI_FP;

// Digit conversions
var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
var BI_RC = new Array();
var rr,vv;
rr = "0".charCodeAt(0);
for(vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
rr = "a".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
rr = "A".charCodeAt(0);
for(vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

function int2char(n) { return BI_RM.charAt(n); }
function intAt(s,i) {
  var c = BI_RC[s.charCodeAt(i)];
  return (c==null)?-1:c;
}

// (protected) copy this to r
function bnpCopyTo(r) {
  for(var i = this.t-1; i >= 0; --i) r[i] = this[i];
  r.t = this.t;
  r.s = this.s;
}

// (protected) set from integer value x, -DV <= x < DV
function bnpFromInt(x) {
  this.t = 1;
  this.s = (x<0)?-1:0;
  if(x > 0) this[0] = x;
  else if(x < -1) this[0] = x+DV;
  else this.t = 0;
}

// return bigint initialized to value
function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

// (protected) set from string and radix
function bnpFromString(s,b) {
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 256) k = 8; // byte array
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else { this.fromRadix(s,b); return; }
  this.t = 0;
  this.s = 0;
  var i = s.length, mi = false, sh = 0;
  while(--i >= 0) {
    var x = (k==8)?s[i]&0xff:intAt(s,i);
    if(x < 0) {
      if(s.charAt(i) == "-") mi = true;
      continue;
    }
    mi = false;
    if(sh == 0)
      this[this.t++] = x;
    else if(sh+k > this.DB) {
      this[this.t-1] |= (x&((1<<(this.DB-sh))-1))<<sh;
      this[this.t++] = (x>>(this.DB-sh));
    }
    else
      this[this.t-1] |= x<<sh;
    sh += k;
    if(sh >= this.DB) sh -= this.DB;
  }
  if(k == 8 && (s[0]&0x80) != 0) {
    this.s = -1;
    if(sh > 0) this[this.t-1] |= ((1<<(this.DB-sh))-1)<<sh;
  }
  this.clamp();
  if(mi) BigInteger.ZERO.subTo(this,this);
}

// (protected) clamp off excess high words
function bnpClamp() {
  var c = this.s&this.DM;
  while(this.t > 0 && this[this.t-1] == c) --this.t;
}

// (public) return string representation in given radix
function bnToString(b) {
  if(this.s < 0) return "-"+this.negate().toString(b);
  var k;
  if(b == 16) k = 4;
  else if(b == 8) k = 3;
  else if(b == 2) k = 1;
  else if(b == 32) k = 5;
  else if(b == 4) k = 2;
  else return this.toRadix(b);
  var km = (1<<k)-1, d, m = false, r = "", i = this.t;
  var p = this.DB-(i*this.DB)%k;
  if(i-- > 0) {
    if(p < this.DB && (d = this[i]>>p) > 0) { m = true; r = int2char(d); }
    while(i >= 0) {
      if(p < k) {
        d = (this[i]&((1<<p)-1))<<(k-p);
        d |= this[--i]>>(p+=this.DB-k);
      }
      else {
        d = (this[i]>>(p-=k))&km;
        if(p <= 0) { p += this.DB; --i; }
      }
      if(d > 0) m = true;
      if(m) r += int2char(d);
    }
  }
  return m?r:"0";
}

// (public) -this
function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

// (public) |this|
function bnAbs() { return (this.s<0)?this.negate():this; }

// (public) return + if this > a, - if this < a, 0 if equal
function bnCompareTo(a) {
  var r = this.s-a.s;
  if(r != 0) return r;
  var i = this.t;
  r = i-a.t;
  if(r != 0) return r;
  while(--i >= 0) if((r=this[i]-a[i]) != 0) return r;
  return 0;
}

// returns bit length of the integer x
function nbits(x) {
  var r = 1, t;
  if((t=x>>>16) != 0) { x = t; r += 16; }
  if((t=x>>8) != 0) { x = t; r += 8; }
  if((t=x>>4) != 0) { x = t; r += 4; }
  if((t=x>>2) != 0) { x = t; r += 2; }
  if((t=x>>1) != 0) { x = t; r += 1; }
  return r;
}

// (public) return the number of bits in "this"
function bnBitLength() {
  if(this.t <= 0) return 0;
  return this.DB*(this.t-1)+nbits(this[this.t-1]^(this.s&this.DM));
}

// (protected) r = this << n*DB
function bnpDLShiftTo(n,r) {
  var i;
  for(i = this.t-1; i >= 0; --i) r[i+n] = this[i];
  for(i = n-1; i >= 0; --i) r[i] = 0;
  r.t = this.t+n;
  r.s = this.s;
}

// (protected) r = this >> n*DB
function bnpDRShiftTo(n,r) {
  for(var i = n; i < this.t; ++i) r[i-n] = this[i];
  r.t = Math.max(this.t-n,0);
  r.s = this.s;
}

// (protected) r = this << n
function bnpLShiftTo(n,r) {
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<cbs)-1;
  var ds = Math.floor(n/this.DB), c = (this.s<<bs)&this.DM, i;
  for(i = this.t-1; i >= 0; --i) {
    r[i+ds+1] = (this[i]>>cbs)|c;
    c = (this[i]&bm)<<bs;
  }
  for(i = ds-1; i >= 0; --i) r[i] = 0;
  r[ds] = c;
  r.t = this.t+ds+1;
  r.s = this.s;
  r.clamp();
}

// (protected) r = this >> n
function bnpRShiftTo(n,r) {
  r.s = this.s;
  var ds = Math.floor(n/this.DB);
  if(ds >= this.t) { r.t = 0; return; }
  var bs = n%this.DB;
  var cbs = this.DB-bs;
  var bm = (1<<bs)-1;
  r[0] = this[ds]>>bs;
  for(var i = ds+1; i < this.t; ++i) {
    r[i-ds-1] |= (this[i]&bm)<<cbs;
    r[i-ds] = this[i]>>bs;
  }
  if(bs > 0) r[this.t-ds-1] |= (this.s&bm)<<cbs;
  r.t = this.t-ds;
  r.clamp();
}

// (protected) r = this - a
function bnpSubTo(a,r) {
  var i = 0, c = 0, m = Math.min(a.t,this.t);
  while(i < m) {
    c += this[i]-a[i];
    r[i++] = c&this.DM;
    c >>= this.DB;
  }
  if(a.t < this.t) {
    c -= a.s;
    while(i < this.t) {
      c += this[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c += this.s;
  }
  else {
    c += this.s;
    while(i < a.t) {
      c -= a[i];
      r[i++] = c&this.DM;
      c >>= this.DB;
    }
    c -= a.s;
  }
  r.s = (c<0)?-1:0;
  if(c < -1) r[i++] = this.DV+c;
  else if(c > 0) r[i++] = c;
  r.t = i;
  r.clamp();
}

// (protected) r = this * a, r != this,a (HAC 14.12)
// "this" should be the larger one if appropriate.
function bnpMultiplyTo(a,r) {
  var x = this.abs(), y = a.abs();
  var i = x.t;
  r.t = i+y.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < y.t; ++i) r[i+x.t] = x.am(0,y[i],r,i,0,x.t);
  r.s = 0;
  r.clamp();
  if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
}

// (protected) r = this^2, r != this (HAC 14.16)
function bnpSquareTo(r) {
  var x = this.abs();
  var i = r.t = 2*x.t;
  while(--i >= 0) r[i] = 0;
  for(i = 0; i < x.t-1; ++i) {
    var c = x.am(i,x[i],r,2*i,0,1);
    if((r[i+x.t]+=x.am(i+1,2*x[i],r,2*i+1,c,x.t-i-1)) >= x.DV) {
      r[i+x.t] -= x.DV;
      r[i+x.t+1] = 1;
    }
  }
  if(r.t > 0) r[r.t-1] += x.am(i,x[i],r,2*i,0,1);
  r.s = 0;
  r.clamp();
}

// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
// r != q, this != m.  q or r may be null.
function bnpDivRemTo(m,q,r) {
  var pm = m.abs();
  if(pm.t <= 0) return;
  var pt = this.abs();
  if(pt.t < pm.t) {
    if(q != null) q.fromInt(0);
    if(r != null) this.copyTo(r);
    return;
  }
  if(r == null) r = nbi();
  var y = nbi(), ts = this.s, ms = m.s;
  var nsh = this.DB-nbits(pm[pm.t-1]);  // normalize modulus
  if(nsh > 0) { pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
  else { pm.copyTo(y); pt.copyTo(r); }
  var ys = y.t;
  var y0 = y[ys-1];
  if(y0 == 0) return;
  var yt = y0*(1<<this.F1)+((ys>1)?y[ys-2]>>this.F2:0);
  var d1 = this.FV/yt, d2 = (1<<this.F1)/yt, e = 1<<this.F2;
  var i = r.t, j = i-ys, t = (q==null)?nbi():q;
  y.dlShiftTo(j,t);
  if(r.compareTo(t) >= 0) {
    r[r.t++] = 1;
    r.subTo(t,r);
  }
  BigInteger.ONE.dlShiftTo(ys,t);
  t.subTo(y,y); // "negative" y so we can replace sub with am later
  while(y.t < ys) y[y.t++] = 0;
  while(--j >= 0) {
    // Estimate quotient digit
    var qd = (r[--i]==y0)?this.DM:Math.floor(r[i]*d1+(r[i-1]+e)*d2);
    if((r[i]+=y.am(0,qd,r,j,0,ys)) < qd) {  // Try it out
      y.dlShiftTo(j,t);
      r.subTo(t,r);
      while(r[i] < --qd) r.subTo(t,r);
    }
  }
  if(q != null) {
    r.drShiftTo(ys,q);
    if(ts != ms) BigInteger.ZERO.subTo(q,q);
  }
  r.t = ys;
  r.clamp();
  if(nsh > 0) r.rShiftTo(nsh,r);  // Denormalize remainder
  if(ts < 0) BigInteger.ZERO.subTo(r,r);
}

// (public) this mod a
function bnMod(a) {
  var r = nbi();
  this.abs().divRemTo(a,null,r);
  if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
  return r;
}

// Modular reduction using "classic" algorithm
function Classic(m) { this.m = m; }
function cConvert(x) {
  if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
  else return x;
}
function cRevert(x) { return x; }
function cReduce(x) { x.divRemTo(this.m,null,x); }
function cMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
function cSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

Classic.prototype.convert = cConvert;
Classic.prototype.revert = cRevert;
Classic.prototype.reduce = cReduce;
Classic.prototype.mulTo = cMulTo;
Classic.prototype.sqrTo = cSqrTo;

// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
// justification:
//         xy == 1 (mod m)
//         xy =  1+km
//   xy(2-xy) = (1+km)(1-km)
// x[y(2-xy)] = 1-k^2m^2
// x[y(2-xy)] == 1 (mod m^2)
// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
// JS multiply "overflows" differently from C/C++, so care is needed here.
function bnpInvDigit() {
  if(this.t < 1) return 0;
  var x = this[0];
  if((x&1) == 0) return 0;
  var y = x&3;    // y == 1/x mod 2^2
  y = (y*(2-(x&0xf)*y))&0xf;  // y == 1/x mod 2^4
  y = (y*(2-(x&0xff)*y))&0xff;  // y == 1/x mod 2^8
  y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff; // y == 1/x mod 2^16
  // last step - calculate inverse mod DV directly;
  // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
  y = (y*(2-x*y%this.DV))%this.DV;    // y == 1/x mod 2^dbits
  // we really want the negative inverse, and -DV < y < DV
  return (y>0)?this.DV-y:-y;
}

// Montgomery reduction
function Montgomery(m) {
  this.m = m;
  this.mp = m.invDigit();
  this.mpl = this.mp&0x7fff;
  this.mph = this.mp>>15;
  this.um = (1<<(m.DB-15))-1;
  this.mt2 = 2*m.t;
}

// xR mod m
function montConvert(x) {
  var r = nbi();
  x.abs().dlShiftTo(this.m.t,r);
  r.divRemTo(this.m,null,r);
  if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
  return r;
}

// x/R mod m
function montRevert(x) {
  var r = nbi();
  x.copyTo(r);
  this.reduce(r);
  return r;
}

// x = x/R mod m (HAC 14.32)
function montReduce(x) {
  while(x.t <= this.mt2)  // pad x so am has enough room later
    x[x.t++] = 0;
  for(var i = 0; i < this.m.t; ++i) {
    // faster way of calculating u0 = x[i]*mp mod DV
    var j = x[i]&0x7fff;
    var u0 = (j*this.mpl+(((j*this.mph+(x[i]>>15)*this.mpl)&this.um)<<15))&x.DM;
    // use am to combine the multiply-shift-add into one call
    j = i+this.m.t;
    x[j] += this.m.am(0,u0,x,i,0,this.m.t);
    // propagate carry
    while(x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
  }
  x.clamp();
  x.drShiftTo(this.m.t,x);
  if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
}

// r = "x^2/R mod m"; x != r
function montSqrTo(x,r) { x.squareTo(r); this.reduce(r); }

// r = "xy/R mod m"; x,y != r
function montMulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }

Montgomery.prototype.convert = montConvert;
Montgomery.prototype.revert = montRevert;
Montgomery.prototype.reduce = montReduce;
Montgomery.prototype.mulTo = montMulTo;
Montgomery.prototype.sqrTo = montSqrTo;

// (protected) true iff this is even
function bnpIsEven() { return ((this.t>0)?(this[0]&1):this.s) == 0; }

// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
function bnpExp(e,z) {
  if(e > 0xffffffff || e < 1) return BigInteger.ONE;
  var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
  g.copyTo(r);
  while(--i >= 0) {
    z.sqrTo(r,r2);
    if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
    else { var t = r; r = r2; r2 = t; }
  }
  return z.revert(r);
}

// (public) this^e % m, 0 <= e < 2^32
function bnModPowInt(e,m) {
  var z;
  if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
  return this.exp(e,z);
}

// protected
BigInteger.prototype.copyTo = bnpCopyTo;
BigInteger.prototype.fromInt = bnpFromInt;
BigInteger.prototype.fromString = bnpFromString;
BigInteger.prototype.clamp = bnpClamp;
BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
BigInteger.prototype.drShiftTo = bnpDRShiftTo;
BigInteger.prototype.lShiftTo = bnpLShiftTo;
BigInteger.prototype.rShiftTo = bnpRShiftTo;
BigInteger.prototype.subTo = bnpSubTo;
BigInteger.prototype.multiplyTo = bnpMultiplyTo;
BigInteger.prototype.squareTo = bnpSquareTo;
BigInteger.prototype.divRemTo = bnpDivRemTo;
BigInteger.prototype.invDigit = bnpInvDigit;
BigInteger.prototype.isEven = bnpIsEven;
BigInteger.prototype.exp = bnpExp;

// public
BigInteger.prototype.toString = bnToString;
BigInteger.prototype.negate = bnNegate;
BigInteger.prototype.abs = bnAbs;
BigInteger.prototype.compareTo = bnCompareTo;
BigInteger.prototype.bitLength = bnBitLength;
BigInteger.prototype.mod = bnMod;
BigInteger.prototype.modPowInt = bnModPowInt;

// "constants"
BigInteger.ZERO = nbv(0);
BigInteger.ONE = nbv(1);

// Depends on jsbn.js and rng.js

// Version 1.1: support utf-8 encoding in pkcs1pad2

// convert a (hex) string to a bignum object
function parseBigInt(str,r) {
  return new BigInteger(str,r);
}

function linebrk(s,n) {
  var ret = "";
  var i = 0;
  while(i + n < s.length) {
    ret += s.substring(i,i+n) + "\n";
    i += n;
  }
  return ret + s.substring(i,s.length);
}

function byte2Hex(b) {
  if(b < 0x10)
    return "0" + b.toString(16);
  else
    return b.toString(16);
}

// PKCS#1 (type 2, random) pad input string s to n bytes, and return a bigint
function pkcs1pad2(s,n) {
  if(n < s.length + 11) { // TODO: fix for utf-8
    alert("Message too long for RSA");
    return null;
  }
  var ba = new Array();
  var i = s.length - 1;
  while(i >= 0 && n > 0) {
    var c = s.charCodeAt(i--);
    if(c < 128) { // encode using utf-8
      ba[--n] = c;
    }
    else if((c > 127) && (c < 2048)) {
      ba[--n] = (c & 63) | 128;
      ba[--n] = (c >> 6) | 192;
    }
    else {
      ba[--n] = (c & 63) | 128;
      ba[--n] = ((c >> 6) & 63) | 128;
      ba[--n] = (c >> 12) | 224;
    }
  }
  ba[--n] = 0;
  var rng = new SecureRandom();
  var x = new Array();
  while(n > 2) { // random non-zero pad
    x[0] = 0;
    while(x[0] == 0) rng.nextBytes(x);
    ba[--n] = x[0];
  }
  ba[--n] = 2;
  ba[--n] = 0;
  return new BigInteger(ba);
}

// "empty" RSA key constructor
function RSAKey() {
  this.n = null;
  this.e = 0;
  this.d = null;
  this.p = null;
  this.q = null;
  this.dmp1 = null;
  this.dmq1 = null;
  this.coeff = null;
}

// Set the public key fields N and e from hex strings
function RSASetPublic(N,E) {
  if(N != null && E != null && N.length > 0 && E.length > 0) {
    this.n = parseBigInt(N,16);
    this.e = parseInt(E,16);
  }
  else
    alert("Invalid RSA public key");
}

// Perform raw public operation on "x": return x^e (mod n)
function RSADoPublic(x) {
  return x.modPowInt(this.e, this.n);
}

// Return the PKCS#1 RSA encryption of "text" as an even-length hex string
function RSAEncrypt(text) {
  var m = pkcs1pad2(text,(this.n.bitLength()+7)>>3);
  if(m == null) return null;
  var c = this.doPublic(m);
  if(c == null) return null;
  var h = c.toString(16);
  if((h.length & 1) == 0) return h; else return "0" + h;
}

// Return the PKCS#1 RSA encryption of "text" as a Base64-encoded string
//function RSAEncryptB64(text) {
//  var h = this.encrypt(text);
//  if(h) return hex2b64(h); else return null;
//}

// protected
RSAKey.prototype.doPublic = RSADoPublic;

// public
RSAKey.prototype.setPublic = RSASetPublic;
RSAKey.prototype.encrypt = RSAEncrypt;
//RSAKey.prototype.encrypt_b64 = RSAEncryptB64;

// Random number generator - requires a PRNG backend, e.g. prng4.js

// For best results, put code like
// <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
// in your main HTML document.

var rng_state;
var rng_pool;
var rng_pptr;

// Mix in a 32-bit integer into the pool
function rng_seed_int(x) {
  rng_pool[rng_pptr++] ^= x & 255;
  rng_pool[rng_pptr++] ^= (x >> 8) & 255;
  rng_pool[rng_pptr++] ^= (x >> 16) & 255;
  rng_pool[rng_pptr++] ^= (x >> 24) & 255;
  if(rng_pptr >= rng_psize) rng_pptr -= rng_psize;
}

// Mix in the current time (w/milliseconds) into the pool
function rng_seed_time() {
  rng_seed_int(new Date().getTime());
}

// Initialize the pool with junk if needed.
if(rng_pool == null) {
  rng_pool = new Array();
  rng_pptr = 0;
  var t;
  if(navigator.appName == "Netscape" && navigator.appVersion < "5" && window.crypto) {
    // Extract entropy (256 bits) from NS4 RNG if available
    var z = window.crypto.random(32);
    for(t = 0; t < z.length; ++t)
      rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
  }  
  while(rng_pptr < rng_psize) {  // extract some randomness from Math.random()
    t = Math.floor(65536 * Math.random());
    rng_pool[rng_pptr++] = t >>> 8;
    rng_pool[rng_pptr++] = t & 255;
  }
  rng_pptr = 0;
  rng_seed_time();
  //rng_seed_int(window.screenX);
  //rng_seed_int(window.screenY);
}

function rng_get_byte() {
  if(rng_state == null) {
    rng_seed_time();
    rng_state = prng_newstate();
    rng_state.init(rng_pool);
    for(rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
      rng_pool[rng_pptr] = 0;
    rng_pptr = 0;
    //rng_pool = null;
  }
  // TODO: allow reseeding after first request
  return rng_state.next();
}

function rng_get_bytes(ba) {
  var i;
  for(i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
}

function SecureRandom() {}

SecureRandom.prototype.nextBytes = rng_get_bytes;

// prng4.js - uses Arcfour as a PRNG

function Arcfour() {
  this.i = 0;
  this.j = 0;
  this.S = new Array();
}

// Initialize arcfour context from key, an array of ints, each from [0..255]
function ARC4init(key) {
  var i, j, t;
  for(i = 0; i < 256; ++i)
    this.S[i] = i;
  j = 0;
  for(i = 0; i < 256; ++i) {
    j = (j + this.S[i] + key[i % key.length]) & 255;
    t = this.S[i];
    this.S[i] = this.S[j];
    this.S[j] = t;
  }
  this.i = 0;
  this.j = 0;
}

function ARC4next() {
  var t;
  this.i = (this.i + 1) & 255;
  this.j = (this.j + this.S[this.i]) & 255;
  t = this.S[this.i];
  this.S[this.i] = this.S[this.j];
  this.S[this.j] = t;
  return this.S[(t + this.S[this.i]) & 255];
}

Arcfour.prototype.init = ARC4init;
Arcfour.prototype.next = ARC4next;

// Plug in your RNG constructor here
function prng_newstate() {
  return new Arcfour();
}

// Pool size must be a multiple of 4 and greater than 32.
// An array of bytes the size of the pool will be passed to init()
var rng_psize = 256;

var b64map="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
var b64pad="=";

function hex2b64(h) {
  var i;
  var c;
  var ret = "";
  for(i = 0; i+3 <= h.length; i+=3) {
    c = parseInt(h.substring(i,i+3),16);
    ret += b64map.charAt(c >> 6) + b64map.charAt(c & 63);
  }
  if(i+1 == h.length) {
    c = parseInt(h.substring(i,i+1),16);
    ret += b64map.charAt(c << 2);
  }
  else if(i+2 == h.length) {
    c = parseInt(h.substring(i,i+2),16);
    ret += b64map.charAt(c >> 2) + b64map.charAt((c & 3) << 4);
  }
  while((ret.length & 3) > 0) ret += b64pad;
  return ret;
}

// convert a base64 string to hex
function b64tohex(s) {
  var ret = ""
  var i;
  var k = 0; // b64 state, 0-3
  var slop;
  for(i = 0; i < s.length; ++i) {
    if(s.charAt(i) == b64pad) break;
    v = b64map.indexOf(s.charAt(i));
    if(v < 0) continue;
    if(k == 0) {
      ret += int2char(v >> 2);
      slop = v & 3;
      k = 1;
    }
    else if(k == 1) {
      ret += int2char((slop << 2) | (v >> 4));
      slop = v & 0xf;
      k = 2;
    }
    else if(k == 2) {
      ret += int2char(slop);
      ret += int2char(v >> 2);
      slop = v & 3;
      k = 3;
    }
    else {
      ret += int2char((slop << 2) | (v >> 4));
      ret += int2char(v & 0xf);
      k = 0;
    }
  }
  if(k == 1)
    ret += int2char(slop << 2);
  return ret;
}

// convert a base64 string to a byte/number array
function b64toBA(s) {
  //piggyback on b64tohex for now, optimize later
  var h = b64tohex(s);
  var i;
  var a = new Array();
  for(i = 0; 2*i < h.length; ++i) {
    a[i] = parseInt(h.substring(2*i,2*i+2),16);
  }
  return a;
}

UTF8 = {
    encode: function (a) {
        for (var b, c = -1, d = (a = a.split("")).length, e = String.fromCharCode; ++c < d; a[c] = (b = a[c].charCodeAt(0)) >= 127 ? e(192 | b >>> 6) + e(128 | b & 63) : a[c]);
        return a.join("")
    },
    decode: function (a) {
        for (var b, c, d = -1, e = (a = a.split("")).length, f = String.fromCharCode; ++d < e;
        (b = a[d].charCodeAt(0)) & 128 && (a[d] = (b & 252) == 192 && ((c = a[d + 1].charCodeAt(0)) & 192) == 128 ? f(((b & 3) << 6) + (c & 63)) : f(128), a[++d] = ""));
        return a.join("")
    }
};

// End of encryption code

if (!window.console) { 
  window.console = {
    log: function(obj){ /* define IE logging function here, or leave empty */ }
  };
}


/*for contact importer*/

(function($) {
  $.fn.sortElements = (function(){
      var sort = [].sort;
      return function(comparator, getSortable) {
          getSortable = getSortable || function(){return this;};
          var placements = this.map(function(){
              var sortElement = getSortable.call(this),
                  parentNode = sortElement.parentNode,
                  nextSibling = parentNode.insertBefore(
                      document.createTextNode(''),
                      sortElement.nextSibling
                  );
              return function() {
                  if (parentNode === this) {
                      throw new Error(
                          "You can't sort elements if any one is a descendant of another."
                      );
                  }
                  parentNode.insertBefore(this, nextSibling);
                  parentNode.removeChild(nextSibling);
              };
          });
          return sort.call(this, comparator).each(function(i){
              placements[i].call(getSortable.call(this));
          });
      };
  })();

  $.extend($.expr[":"], {
    containsIgnoreCase: function (a, b, c) {
      return (a.textContent || a.innerText || "").toLowerCase().indexOf((c[3] || "").toLowerCase()) >= 0
    }
  });

  $.fn.listFilter = function() {
    var list = this;
    input = $("<input>").attr({"class":"filterinput", "type":"text"});
    input.keydown(function(e) {
      switch(e.keyCode) {
      case 27:
        input.val("");
      }
    }).keyup(function() {
      list.find("li").not(list.find("li *:containsIgnoreCase('" + this.value + "')").closest("li").show()).hide();
    });
    list.before(input);
    return list;
  }

  $.fn.encryptPassword = function (a) {
      if (this.length <= 0) return this;
      a = $.extend({
          password: "input[type=password]",
          hiddenPassword: "input[type=hidden][name=hidden_pass]"
      }, a);
      var b = this.find(a.password),
          c = this.find(a.hiddenPassword);
      a = function () {
          if (b.val().length > 0) {
              var d = linebrk(hex2b64(RSA.encrypt(UTF8.encode(b.val()))), 64);
              b.val("");
              c.val(d)
          }
      };
      a();
      this.bind({
          "ajax:before": a,
          submit: a
      });
      return this
  };

  $.fn.contactImporter = function() {
    var importer = $('<div>'), $this = this, 
        importerExists = $this.hasClass('.contact-importer');

    if ($this.length == 0) return false;

    initialize = function(data) {
      importer = $(data.partial).appendTo(importer.empty());
      actions.update('count');
      actions.update('sort');

      if (data.count > 0) actions.show('contacts');

      importer.find('ul').listFilter();
      importer.find('div[action-skip]').click(function() { 
        actions.show('contacts'); 
      });
      importer.find('a[action-invite], div[action-invite]').click(function() { 
        actions.show('login'); 
      });
      importer.delegate("li:not(.empty)", "click", function () {
        $(this).toggleClass("selected");
      });
      importer.delegate("span.select_all", "click", function() {
        importer.find('li').not('.empty, .selected').addClass('selected');
      });
      importer.delegate("span.select_none", "click", function() {
        importer.find('li.selected').removeClass('selected');
      });
      importer.delegate("span.select_all, span.select_none, li:not(.empty)", "click", function() {
        actions.update('count');
      });
      importer.delegate("[action-invite], li, span.select_all, span.select_none, input, .link", "click", function() {
        $('.error, .success, .import_error').fadeOut();
      });
      importer.find('form').bind({
        'ajax:before': function() {
          importer.find('.processing').show();
          $(this).find("input[type=submit]").attr('disabled', 'disabled');
        },
        'ajax:complete': function() {
          importer.find('.processing').hide();
          $(this).find("input[type=submit]").removeAttr('disabled');
        },
        'ajax:failure': function(obj, xhr) {
          var obj = $.parseJSON(xhr.responseText);
          $('.error, .import_error').html(obj.errors).fadeIn();
          $(this).find("input[type=submit]").removeAttr('disabled');
        }
      });
      importer.find('form[form-action=add-contact]').bind({
        'ajax:success': function(obj, jsonData) {
          importer.find('li.empty').remove();
          var obj = $.parseJSON(jsonData);
          $(obj.partial).appendTo(importer.find('ul'));
          $("input[type=text]", this).val("");
          $('.success').html(obj.message).fadeIn();
          actions.update('count')
          actions.update('sort');
        } 
      });
      importer.find('form[form-action=import]').encryptPassword().bind({
        'ajax:success': function(obj, jsonData) {
          var obj = $.parseJSON(jsonData);
          $(obj.partial).appendTo(importer.find('ul').empty());
          actions.update('count')
          actions.update('sort')
          actions.show('contacts');
        }
      });
      importer.find('form[form-action=share]').bind('submit', function() {
        var emails = [];
        $('.selected').each(function() {
          emails.push( $(this).find('.email').text() );
        });
        $(this).find("input[name='referral[emails]']").empty().val(emails.join(', ') || "");
      });
      importer.find('form[form-action=share]').bind({
        'ajax:success': function(obj, jsonData) {
          var obj = $.parseJSON(jsonData);
          if (obj.message) $('.success').html(obj.message).fadeIn();
        } 
      });
      importer.find("form input[type=submit]").unbind("click.iefix").bind("click.iefix", function (f) {
          f.preventDefault();
          $(this).closest("form").submit()
      });
    }

    actions = {
      show: function(state) {
        switch(state) {
        case 'login':  
          importer.find('.improsys_login').show();
          importer.find('.contacts').hide();
          break;
        case 'contacts':
          importer.find('.improsys_login').hide();
          importer.find('.contacts').show();
        }
      },
      update: function(action) {
        switch(action) {
        case 'count':
          importer.find(".count").html(importer.find("li.selected").length + " Selected")
          break;
        case 'sort':
          importer.find('ul').find('li').sortElements(function(a, b) { 
            return a.getAttribute('data-sort').toLowerCase() > b.getAttribute('data-sort').toLowerCase() ? 1 : -1
          });
        }
      }
    }

    if (importerExists) {
    
    } else {
      importer.html('Loading...');
      $.getJSON('/contacts/new', parseParams($this.attr("href")), function(data) {
        initialize(data);
      })
    }
    return importer;
  }
})(jQuery);

var params = function(){
  return parseParams(window.location.search);
}();

function parseParams(url) {
  url = url || "";
  if(url.split('?').length === 1) return {}
  var params = {}, pairs = url.split('?')[1].split('&')

  for (i=0;i<pairs.length;i++) {
    key_value_pair = pairs[i].split('=');
    params[key_value_pair[0]] = key_value_pair[1];
  } return params;
};

jQuery.noConflict();

(function($) { 
    
  $.ajaxSetup({
    'beforeSend': function(xhr) { xhr.setRequestHeader("Accept", "text/javascript, application/json, text/html, application/xml, text/xml, */*") }
  });

  $(document).ready(function() {

    $('#share_deal').click( function() {
      $.facebox($(this).contactImporter());
      return false;
    });

    $('a.contact-importer').each(function() {
      $(this).after($(this).contactImporter());
    });

    $('a[rel*=facebox]').facebox();

    $('.scrollable').scrollable({circular: 'true', speed: 1000}).autoscroll(4500).navigator();
    $(".navi td:first").click(); 

    $('.scroller').livequery(function() {
      $(this).scrollable({circular: 'false', speed: 1000}).navigator();
      $('.check').addClass('active');
    });

    $('ul#packages label').each( function(){
      $(this).click( function(){
        $(this).attr('class', ($("input[type=checkbox]", $(this)).attr('checked'))? 'checked' : 'unchecked') 
      })
    })

    $('.gift_cards-new .amounts label').click(function(event) {
      $('.gift_cards-new .amounts label')
        .addClass('amount')
        .css('background-position', '0 0')

      $(this).removeClass('amount').css('background-position', '0 -49px')
    });

    $('a.tab').click(function(event) {
      $('a.tab[class*=active]').removeClass('active');
      $('.panel').hide();
      var $this_panel = $('#' + this.href.split('#')[1]);
      $this_panel.show();

      $(this).addClass('active');
      event.preventDefault();
    });

    if (params) $('a[href*='+params['tab']+']').click();

    $('.ajax_form').submit(function(event) {
      var $form = $(this);
      var $submit_btn = $form.find("[type=submit]");
      $submit_btn.hide().after('<p class="result">Processing...</p>');
      $.post($form.attr('action') + '?' + $form.serialize(), function(data) { $form.find('.result').html("Sent Successfully!") });
      event.preventDefault();
    });

    $(".msg_body").hide();
    $(".msg_head").click(function() {
      if ($(this).attr("class") == "msg_head")
        $(this).attr("class", "msg_head less");
      else
        $(this).attr("class", "msg_head");
      $(this).next(".msg_body").slideToggle({duration:'slow', easing: 'linear'});
    });

    $(".msg_list .msg_head:first").click(); 

    // disable multiple clicking of button
    $('.participations-create .submit_field input').click( function() { 
      $(this).hide().after('<p>Processing...</p><em>Please wait for your confirmation</em>'); 
    });

    $('.gift_cards-new .amounts input').click(function() { 
      $('#gift_card_value_preview').attr('src', '/images/gift-cards/value-'+this.value+'.png'); 
    });	
  });

  $.fn.extend({
    highlightAsError: function() {
      return this.addClass('has_error');
    },

    isValidEmail: function() {
      return /^((([a-z]|\d|[!#\$%&'\*\+\-\/=\?\^_`{\|}~]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])+(\.([a-z]|\d|[!#\$%&'\*\+\-\/=\?\^_`{\|}~]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])+)*)|((\x22)((((\x20|\x09)*(\x0d\x0a))?(\x20|\x09)+)?(([\x01-\x08\x0b\x0c\x0e-\x1f\x7f]|\x21|[\x23-\x5b]|[\x5d-\x7e]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(\\([\x01-\x09\x0b\x0c\x0d-\x7f]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF]))))*(((\x20|\x09)*(\x0d\x0a))?(\x20|\x09)+)?(\x22)))@((([a-z]|\d|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(([a-z]|\d|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])*([a-z]|\d|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])))\.)+(([a-z]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])|(([a-z]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])([a-z]|\d|-|\.|_|~|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])*([a-z]|[\u00A0-\uD7FF\uF900-\uFDCF\uFDF0-\uFFEF])))\.?$/i.test($(this).val());
    },

    isValidFiveDigitZipcode: function() {
      return /^\d{5}$/.test($(this).val());
    },

    hasCityInterests: function() {
      return $(this).find('input:checked').length > 0 ? true : false;
    }
  });

  $.facebox = function(data, klass) {
    $.facebox.loading()

    if (data.ajax) fillFaceboxFromAjax(data.ajax)
    else if (data.image) fillFaceboxFromImage(data.image)
    else if (data.div) fillFaceboxFromHref(data.div)
    else if ($.isFunction(data)) data.call($)
    else $.facebox.reveal(data, klass)
  }

  /*
   * Public, $.facebox methods
   */

  $.extend($.facebox, {
    settings: {
      opacity      : 0,
      overlay      : true,
      loadingImage : 'http://www.buywithme.com/facebox/loading.gif',
      closeImage   : 'http://www.buywithme.com/facebox/closelabel.gif',
      imageTypes   : [ 'png', 'jpg', 'jpeg', 'gif' ],
      faceboxHtml  : '\
    <div id="facebox" style="display:none;"> \
      <div class="popup"> \
        <table> \
          <tbody> \
            <tr> \
              <td class="tl"/><td class="b"/><td class="tr"/> \
            </tr> \
            <tr> \
              <td class="b"/> \
              <td class="body"> \
                <div class="content"> \
                </div> \
                <div class="footer"> \
                  <a href="#" class="close"> \
                    <img src="/images/facebox/closelabel.gif" title="close" class="close_image" /> \
                  </a> \
                </div> \
              </td> \
              <td class="b"/> \
            </tr> \
            <tr> \
              <td class="bl"/><td class="b"/><td class="br"/> \
            </tr> \
          </tbody> \
        </table> \
      </div> \
    </div>'
    },

    loading: function() {
      init()
      if ($('#facebox .loading').length == 1) return true
      showOverlay()

      $('#facebox .content').empty()
      $('#facebox .body').children().hide().end().
        append('<div class="loading"><img src="'+$.facebox.settings.loadingImage+'"/></div>')

      $('#facebox').css({
        top:	getPageScroll()[1] + (getPageHeight() / 10),
        left:	385.5
      }).show()

      $(document).bind('keydown.facebox', function(e) {
        if (e.keyCode == 27) $.facebox.close()
        return true
      })
      $(document).trigger('loading.facebox')
    },

    reveal: function(data, klass) {
      $(document).trigger('beforeReveal.facebox')
      if (klass) $('#facebox .content').addClass(klass)
      $('#facebox .content').append(data)
      $('#facebox .loading').remove()
      $('#facebox .body').children().fadeIn('normal')
      $('#facebox').css('left', $(window).width() / 2 - ($('#facebox table').width() / 2))
      $(document).trigger('reveal.facebox').trigger('afterReveal.facebox')
    },

    close: function() {
      $(document).trigger('close.facebox')
      return false
    }
  })

  /*
   * Public, $.fn methods
   */

  $.fn.facebox = function(settings) {
    init(settings)

    function clickHandler() {
      $.facebox.loading(true)

      // support for rel="facebox.inline_popup" syntax, to add a class
      // also supports deprecated "facebox[.inline_popup]" syntax
      var klass = this.rel.match(/facebox\[?\.(\w+)\]?/)
      if (klass) klass = klass[1]

      fillFaceboxFromHref(this.href, klass)
      return false
    }

    return this.click(clickHandler)
  }

  /*
   * Private methods
   */

  // called one time to setup facebox on this page
  function init(settings) {
    if ($.facebox.settings.inited) return true
    else $.facebox.settings.inited = true

    $(document).trigger('init.facebox')
    makeCompatible()

    var imageTypes = $.facebox.settings.imageTypes.join('|')
    $.facebox.settings.imageTypesRegexp = new RegExp('\.' + imageTypes + '$', 'i')

    if (settings) $.extend($.facebox.settings, settings)
    $('body').append($.facebox.settings.faceboxHtml)

    var preload = [ new Image(), new Image() ]
    preload[0].src = $.facebox.settings.closeImage
    preload[1].src = $.facebox.settings.loadingImage

    $('#facebox').find('.b:first, .bl, .br, .tl, .tr').each(function() {
      preload.push(new Image())
      preload.slice(-1).src = $(this).css('background-image').replace(/url\((.+)\)/, '$1')
    })

    $('#facebox .close').click($.facebox.close)
    $('#facebox .close_image').attr('src', $.facebox.settings.closeImage)
  }
  
  // getPageScroll() by quirksmode.com
  function getPageScroll() {
    var xScroll, yScroll;
    if (self.pageYOffset) {
      yScroll = self.pageYOffset;
      xScroll = self.pageXOffset;
    } else if (document.documentElement && document.documentElement.scrollTop) {	 // Explorer 6 Strict
      yScroll = document.documentElement.scrollTop;
      xScroll = document.documentElement.scrollLeft;
    } else if (document.body) {// all other Explorers
      yScroll = document.body.scrollTop;
      xScroll = document.body.scrollLeft;	
    }
    return new Array(xScroll,yScroll) 
  }

  // Adapted from getPageSize() by quirksmode.com
  function getPageHeight() {
    var windowHeight
    if (self.innerHeight) {	// all except Explorer
      windowHeight = self.innerHeight;
    } else if (document.documentElement && document.documentElement.clientHeight) { // Explorer 6 Strict Mode
      windowHeight = document.documentElement.clientHeight;
    } else if (document.body) { // other Explorers
      windowHeight = document.body.clientHeight;
    }	
    return windowHeight
  }

  // Backwards compatibility
  function makeCompatible() {
    var $s = $.facebox.settings

    $s.loadingImage = $s.loading_image || $s.loadingImage
    $s.closeImage = $s.close_image || $s.closeImage
    $s.imageTypes = $s.image_types || $s.imageTypes
    $s.faceboxHtml = $s.facebox_html || $s.faceboxHtml
  }

  // Figures out what you want to display and displays it
  // formats are:
  //     div: #id
  //   image: blah.extension
  //    ajax: anything else
  function fillFaceboxFromHref(href, klass) {
    // div
    if (href.match(/#/)) {
      var url    = window.location.href.split('#')[0]
      var target = href.replace(url,'')
      $.facebox.reveal($(target).clone().show(), klass)

    // image
    } else if (href.match($.facebox.settings.imageTypesRegexp)) {
      fillFaceboxFromImage(href, klass)
    // ajax
    } else {
      fillFaceboxFromAjax(href, klass)
    }
  }

  function fillFaceboxFromImage(href, klass) {
    var image = new Image()
    image.onload = function() {
      $.facebox.reveal('<div class="image"><img src="' + image.src + '" /></div>', klass)
    }
    image.src = href
  }

  function fillFaceboxFromAjax(href, klass) {
    $.get(href, function(data) { $.facebox.reveal(data, klass) })
    showHowItWorks();
  }

  function skipOverlay() {
    return $.facebox.settings.overlay == false || $.facebox.settings.opacity === null 
  }

  function showOverlay() {
    if (skipOverlay()) return

    if ($('facebox_overlay').length == 0) 
      $("body").append('<div id="facebox_overlay" class="facebox_hide"></div>')

    $('#facebox_overlay').hide().addClass("facebox_overlayBG")
      .css('opacity', $.facebox.settings.opacity)
      .click(function() { $(document).trigger('close.facebox') })
      .fadeIn(200)
    return false
  }

  function hideOverlay() {
    if (skipOverlay()) return

    $('#facebox_overlay').fadeOut(200, function(){
      $("#facebox_overlay").removeClass("facebox_overlayBG")
      $("#facebox_overlay").addClass("facebox_hide") 
      $("#facebox_overlay").remove()
    })
    
    return false
  }

  /*
   * Bindings
   */

  $(document).bind('close.facebox', function() {
    $(document).unbind('keydown.facebox')
    $('#facebox').fadeOut(function() {
      $('#facebox .content').removeClass().addClass('content')
      hideOverlay()
      $('#facebox .loading').remove()
    })
  })
})(jQuery);


function trackShare(action, param) {
  _gaq.push(['_trackEvent', 'Share', action, param]);
}

CitySelector = Class.create({
  initialize:
    function(input) {
      this.button = $(input);
      this.dropdown = $('city_selector_cities');
      this.observe();
    },

  hide:
    function() {
      this.dropdown.hide();
      this.button.removeClassName('active');
      Event.stopObserving(document, 'click', this.boundClick);
    },

  show:
    function() {
      this.dropdown.show();
      this.button.addClassName('active');
      this.boundClick = this.handleDocumentClick.bind(this);
      Event.observe(document, 'click', this.boundClick);
    },

  toggle:
    function() {
      if(this.visible()) { this.hide(); } else { this.show(); }
    },

  visible:
    function() {
      return this.dropdown.visible();
    },

  observe:
    function() {
      this.button.observe('click', this.toggle.bind(this));
    },

  handleDocumentClick:
    function(event) {
      var element = Event.element(event);
      if(!element.descendantOf(this.dropdown) && element != this.button) {
        this.hide();
      }
    }
});

Event.observe(window, 'load', function() {
  $$('.choose_your_city').each(function(element) {
    new CitySelector(element);
  });
});

DealTimer = Class.create({
  initialize:
    function(element) {
      this.element = $(element);
      this.deadline = new Date(this.element.readAttribute("title"));
      new PeriodicalExecuter(this.update.bind(this), 1);
      this.update();
    },

  update:
    function() {
      var msPerDay = 24 * 60 * 60 * 1000,
          timeLeft = (this.deadline.getTime() - new Date()),

          e_daysLeft = timeLeft / msPerDay,
          daysLeft = Math.floor(e_daysLeft),

          e_hrsLeft = (e_daysLeft - daysLeft)*24,
          hrsLeft = Math.floor(e_hrsLeft),

		  e_minsLeft = (e_hrsLeft - hrsLeft)*60,
          minsLeft = Math.floor(e_minsLeft),

		  e_secsLeft = (e_minsLeft - minsLeft) * 60,
		  secsLeft = Math.floor(e_secsLeft)

          timerString = "";
      if(daysLeft > 1)  { timerString += daysLeft + " <span class='timerlabels'>days</span> "; }
      if(daysLeft == 1) { timerString += daysLeft + " <span class='timerlabels'>day</span> "; }
      if(hrsLeft > 0)   { timerString += hrsLeft + " <span class='timerlabels'>hr</span> "; }
      if(minsLeft > 0)  { timerString += minsLeft + " <span class='timerlabels'>min</span> "; }
      if(minsLeft == 0 && daysLeft == 0 && hrsLeft == 0 && timeLeft > 0) {
        timerString = "Less than a minute ";
      }

  	  if(daysLeft<1) {
						timerString = hrsLeft + " <span class='timerlabels'>hr</span> " 
						timerString += minsLeft + " <span class='timerlabels'>min</span> "
						timerString += secsLeft + " <span class='timerlabels'>sec</span> "
						}

      if(e_daysLeft < 0) { timerString = "No time "; }
	  timerString += "<span id='remainder_text'>remaining!</span>";
      this.element.update(timerString);
    }
});

Event.observe(document, 'dom:loaded', function() {
  $$('.timer').each(function(element) {
    new DealTimer(element);
  });
});

Event.observe(window, 'load', function() {
  var hash = window.location.hash;

  $$('a.external').each(function(externalLink) {
                          externalLink.writeAttribute('target', '_blank');
                        });
});

function gracefulFacebookLogout() {
  FB.Connect.ifUserConnected(
    function() { FB.Connect.logoutAndRedirect('/logout'); },
    function() { document.location.href = '/logout'; }
  );
}

var participationShare = (function($) {
  var SHARE_TYPES = ["twitter", "facebook", "email"],
      self = {globalTrack: ""},
      showInput = function(type) {
        $.each(SHARE_TYPES, function(index, value) {
          $("#sharing_" + value + "_content").hide();
        });
        $("#sharing_" + type + "_content").show();
      },
      changeClass = function(type) {
        var newClassName = "clearfix " + type + "_active";
        $("#sharing_options_buttons").attr("class", newClassName);
      };

  self.click = function(type) {
    var callback = arguments[1],
        whenClicked = self.whenClicked || "AfterPurchase";

    return function(event) {
      showInput(type);
      changeClass(type);
      if($.isFunction(callback)) {
        callback.call();
      }
      if(self.globalTrack != "") {
        trackShare(type + whenClicked, self.globalTrack);
      }
      return false;
    };
  };

  return self;
})(jQuery);

function setErrorsOnField(id, errors, prettyName) {
  $(id).removeClassName("fieldWithErrors");
  $(id).parentNode.select("div.error").each(function(element) {
    Element.remove(element);
  });
  if(errors.any()) {
    errors.each(function(error) {
      var errorMessage = error[1];
      if(error[0] != "base") {
        errorMessage = (prettyName || error[0]) + " " + error[1];
      }
      $(id).parentNode.insert({"bottom": "<div class='error'>" + errorMessage + "</div>"});
      $(id).addClassName("fieldWithErrors");
    });
  }
}

function generateTotalForParticipation(url) {
  var valueOrZero = function(value) {
    if(value === undefined) {
      return 0;
    }
    return value;
  };

  return function(event) {
    var parameters = $("new_participation").serialize(true);
    if(parameters['participation[cim_payment_profile_key]'] == "on") parameters['participation[cim_payment_profile_key]'] = null;
    
    new Ajax.Request(url,
      {
        method: "post",
        parameters: parameters,
        onSuccess: function(data) {
          var participation = data.responseJSON.participation;

          var subTotal              = parseFloat($("subtotal").innerHTML);
          var discountPercentage    = valueOrZero(participation.discount_percentage);
          var discountAmount        = subTotal * discountPercentage / 100;
          discountAmount           += valueOrZero(participation.discount_amount);
          var subTotalAfterDiscount = Math.max(subTotal - discountAmount, 0);

          var displayTotal          = subTotalAfterDiscount;
          var creditUsed            = 0;

          if ($('credit_on_your_account_total')) {
            var totalCreditOnAccount  = parseFloat($('total_credit_on_account').innerHTML);
            creditUsed                = totalCreditOnAccount;
            if (creditUsed > subTotalAfterDiscount) {
              creditUsed = subTotalAfterDiscount;
            }
            displayTotal -= creditUsed;
            $('credit_on_your_account_total').innerHTML = (totalCreditOnAccount - creditUsed).toFixed(2);
          }

          $("credit_used").value              = creditUsed;
          $("credit_text").innerHTML          = creditUsed.toFixed(2);

          $("discount_amount").value          = discountAmount;
          $("discount_amount_text").innerHTML = discountAmount.toFixed(2);
          $("display_total").innerHTML        = displayTotal.toFixed(2);

          $("discount_message").innerHTML     = "";
          if(discountAmount > 0) {
            $("discount_value").value  = discountAmount;
            $("discount_message").innerHTML = participation.discount_string + " off";
          } else if ($("participation_discount_code_string").value != '') {
            var discountCodeErrors = participation.errors.detect(function(a) { return a[0].match(/discount/); })[1];
            $("discount_message").innerHTML = "Discount Code " + discountCodeErrors;
          }

          if (displayTotal > 0) {
            $("credit_card_information").show();
            $('credit_card_options').show();
            $('free_message').hide();
            $("shipping_information").show();

            if ($('participation_cim_payment_profile_key_1658696').checked) {
              $('confirm_your_password').show();
              $("credit_card_information").hide();
            } else {
              $('confirm_your_password').hide();
              $("credit_card_information").show();
            }
          } else {
            $('confirm_your_password').hide();
            $("credit_card_information").hide();
            $('credit_card_options').hide();
            $('free_message').show();
            $("shipping_information").hide();
          }

          $("credit_total").update("<span>$" + participation.user_total_credit + "</span>");
          $("user-remaining-credit").update("$" + participation.user_remaining_credit);
          $("participation-total-before-discount").update("$" + participation.total_before_discount);
          $("participation-total-before-discount-for-quantity").update("$" + participation.total_before_discount);
        }
      }
    );
    //event.stop(); //removed for IE6 bug
  };
}

function gtrack(url, reference) {
	q = '?';
	try {
		if (url.indexOf('?')==0) {q=''}
		_gaq.push(['_trackPageview', url + q + reference]);
	}
	catch(err)
		{
		// error trapping
		// alert('unable to track\n' + err);
		}
	if (url!=''){self.location.href=url;return false;}

	else {return true;}
}

function update_current_partner_session(partner, atoken) {
	//new Ajax.Request('/admin/partners/set_current_partner')
	new Ajax.Request('/admin/partners/1/set_current_partner', {asynchronous:true, method: 'get', evalScripts:true,
  parameters: {
  	partner: partner, authenticity_token: atoken
  } }
);
}

function setCookie(c_name,value,expiredays)
{
  var exdate=new Date();
  exdate.setDate(exdate.getDate()+expiredays);
  document.cookie=c_name+ "=" +escape(value)+
  ((expiredays==null) ? "" : ";expires="+exdate.toUTCString());
}

function getCookie(c_name)
{
if (document.cookie.length>0)
  {
  c_start=document.cookie.indexOf(c_name + "=");
  if (c_start!=-1)
    {
    c_start=c_start + c_name.length+1;
    c_end=document.cookie.indexOf(";",c_start);
    if (c_end==-1) c_end=document.cookie.length;
    return unescape(document.cookie.substring(c_start,c_end));
    }
  }
return "";
}

