require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.


require import Array1 Array32 Array256.
require import WArray1 WArray256.

abbrev bn_glob_p = Array32.of_list witness [W64.of_int (-1);
W64.of_int 1545454141666273896; W64.of_int 1572361106993317136;
W64.of_int 4149303432552213221; W64.of_int (-2437630513363020008);
W64.of_int (-5348765695191788855); W64.of_int (-7266694737971142001);
W64.of_int (-2045066149513755133); W64.of_int 3643515754058796603;
W64.of_int (-1048094028264365700); W64.of_int 7425368496004700164;
W64.of_int (-7001644933747141011); W64.of_int 2045464732017971899;
W64.of_int (-8978667873486262890); W64.of_int 7572309818504171359;
W64.of_int (-7432548837780761702); W64.of_int (-4467433697928036603);
W64.of_int 5271575865889938237; W64.of_int (-5863928532294754330);
W64.of_int (-1281155366686974043); W64.of_int 864511594326308845;
W64.of_int (-843225458941629077); W64.of_int (-1979976941098336570);
W64.of_int 5755940542857986629; W64.of_int 3470879405153129527;
W64.of_int (-1183011067081899237); W64.of_int 5857503583518590173;
W64.of_int 147421033984662306; W64.of_int 2955010104097229940;
W64.of_int (-4267615245585081135); W64.of_int (-3958705157555305932);
W64.of_int (-1)].


module type Syscall_t = {
  proc randombytes_1(_:W8.t Array1.t) : W8.t Array1.t
  proc randombytes_256(_:W8.t Array256.t) : W8.t Array256.t
}.

module Syscall : Syscall_t = {
  proc randombytes_1(a:W8.t Array1.t) : W8.t Array1.t = {
    a <$ dmap WArray1.darray
         (fun a => Array1.init (fun i => WArray1.get8 a i));
    return a;
  }
  
  proc randombytes_256(a:W8.t Array256.t) : W8.t Array256.t = {
    a <$ dmap WArray256.darray
         (fun a => Array256.init (fun i => WArray256.get8 a i));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc bn_subc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
    var aux: int;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    x1 <- a.[0];
    x2 <- b.[0];
    (cf, x1) <- sbb_64 x1 x2 false;
    a.[0] <- x1;
    i <- 1;
    while (i < 32) {
      x1 <- a.[i];
      x2 <- b.[i];
      (cf, x1) <- sbb_64 x1 x2 cf;
      a.[i] <- x1;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_copy (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var r:W64.t Array32.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    i <- 0;
    while (i < 32) {
      t <- a.[i];
      r.[i] <- t;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_set0 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    
    var i:int;
    
    i <- 0;
    while (i < 32) {
      a.[i] <- (W64.of_int 0);
      i <- i + 1;
    }
    return (a);
  }
  
  proc random_bit_naive () : W8.t = {
    
    var r:W8.t;
    var byte_p:W8.t Array1.t;
    var _byte_p:W8.t Array1.t;
    _byte_p <- witness;
    byte_p <- witness;
    _byte_p <- byte_p;
    byte_p <@ SC.randombytes_1 (_byte_p);
    if ((byte_p.[0] \ult (W8.of_int 128))) {
      r <- (W8.of_int 0);
    } else {
      r <- (W8.of_int 1);
    }
    return (r);
  }
  
  proc random_bit () : W8.t = {
    
    var r:W8.t;
    var byte_p:W8.t Array1.t;
    var _byte_p:W8.t Array1.t;
    _byte_p <- witness;
    byte_p <- witness;
    _byte_p <- byte_p;
    byte_p <@ SC.randombytes_1 (_byte_p);
    r <- byte_p.[0];
    r <- (r `&` (W8.of_int 1));
    return (r);
  }
  
  proc bn_rsample_i (byte_z:W64.t Array32.t) : int * W64.t Array32.t = {
    var aux: W8.t Array256.t;
    
    var i:int;
    var byte_p:W64.t Array32.t;
    var cf:bool;
    var _byte_p:W64.t Array32.t;
    var byte_q:W64.t Array32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    _byte_p <- witness;
    byte_p <- witness;
    byte_q <- witness;
    i <- 0;
    byte_p <@ bn_set0 (byte_p);
    ( _0, cf,  _1,  _2,  _3,  _4) <- set0_64 ;
    
    while ((! cf)) {
      _byte_p <- byte_p;
      aux <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                 (WArray256.init64 (fun i_0 => _byte_p.[i_0]))
                                 i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux.[i_0])) i_0));
      byte_q <@ bn_copy (byte_p);
      (cf, byte_q) <@ bn_subc (byte_q, byte_z);
      i <- (i + 1);
    }
    return (i, byte_p);
  }
  
  proc bn_rsample (byte_z:W64.t Array32.t) : W64.t Array32.t = {
    var aux: W8.t Array256.t;
    
    var byte_p:W64.t Array32.t;
    var i:int;
    var cf:bool;
    var _byte_p:W64.t Array32.t;
    var byte_q:W64.t Array32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:W64.t;
    _byte_p <- witness;
    byte_p <- witness;
    byte_q <- witness;
    i <- 0;
    byte_p <@ bn_set0 (byte_p);
    ( _0, cf,  _1,  _2,  _3,  _4) <- set0_64 ;
    
    while ((! cf)) {
      _byte_p <- byte_p;
      aux <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                 (WArray256.init64 (fun i_0 => _byte_p.[i_0]))
                                 i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux.[i_0])) i_0));
      byte_q <@ bn_copy (byte_p);
      (cf, byte_q) <@ bn_subc (byte_q, byte_z);
      i <- (i + 1);
    }
    return (byte_p);
  }
  
  proc bn_lt_cf (a:W64.t Array32.t, b:W64.t Array32.t) : bool = {
    var aux: int;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    t <- a.[0];
    (cf, t) <- sbb_64 t b.[0] false;
    i <- 1;
    while (i < 32) {
      t <- a.[i];
      (cf, t) <- sbb_64 t b.[i] cf;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc bn_rnd (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: W8.t Array256.t;
    
    var _byte_p:W64.t Array32.t;
    _byte_p <- witness;
    _byte_p <- a;
    aux <@ SC.randombytes_256 ((Array256.init (fun i => get8
                               (WArray256.init64 (fun i => _byte_p.[i])) i)));
    a <-
    (Array32.init (fun i => get64 (WArray256.init8 (fun i => aux.[i])) i));
    return (a);
  }
  
  proc bn_rsample1 (a:W64.t Array32.t, bnd:W64.t Array32.t) : W64.t Array32.t = {
    
    var cf:bool;
    
    a <@ bn_rnd (a);
    cf <@ bn_lt_cf (a, bnd);
    while ((! cf)) {
      a <@ bn_rnd (a);
      cf <@ bn_lt_cf (a, bnd);
    }
    return (a);
  }
}.

