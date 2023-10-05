require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.

from Jasmin require import JLeakage.
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
  var leakages : leakages_t
  
  proc bn_subc (a:W64.t Array32.t, b:W64.t Array32.t) : bool *
                                                        W64.t Array32.t = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var x1:W64.t;
    var x2:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    x1 <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux <- b.[0];
    x2 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    (aux_0, aux) <- sbb_64 x1 x2 false;
    cf <- aux_0;
    x1 <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <- x1;
    leakages <- LeakAddr([0]) :: leakages;
    a.[0] <- aux;
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      x1 <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      aux <- b.[i];
      x2 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      (aux_0, aux) <- sbb_64 x1 x2 cf;
      cf <- aux_0;
      x1 <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux <- x1;
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux;
      i <- i + 1;
    }
    return (cf, a);
  }
  
  proc bn_copy (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var r:W64.t Array32.t;
    var i:int;
    var t:W64.t;
    r <- witness;
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux_0 <- a.[i];
      t <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- t;
      leakages <- LeakAddr([i]) :: leakages;
      r.[i] <- aux_0;
      i <- i + 1;
    }
    return (r);
  }
  
  proc bn_set0 (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux: int;
    var aux_0: W64.t;
    
    var i:int;
    
    leakages <- LeakFor(0,32) :: LeakAddr([]) :: leakages;
    i <- 0;
    while (i < 32) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W64.of_int 0);
      leakages <- LeakAddr([i]) :: leakages;
      a.[i] <- aux_0;
      i <- i + 1;
    }
    return (a);
  }
  
  proc random_bit_naive () : W8.t = {
    var aux_0: W8.t;
    var aux: W8.t Array1.t;
    
    var r:W8.t;
    var byte_p:W8.t Array1.t;
    var _byte_p:W8.t Array1.t;
    _byte_p <- witness;
    byte_p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- byte_p;
    _byte_p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ SC.randombytes_1 (_byte_p);
    byte_p <- aux;
    leakages <- LeakCond((byte_p.[0] \ult (W8.of_int 128))) :: LeakAddr(
    [0]) :: leakages;
    if ((byte_p.[0] \ult (W8.of_int 128))) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W8.of_int 0);
      r <- aux_0;
    } else {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- (W8.of_int 1);
      r <- aux_0;
    }
    return (r);
  }
  
  proc random_bit () : W8.t = {
    var aux_0: W8.t;
    var aux: W8.t Array1.t;
    
    var r:W8.t;
    var byte_p:W8.t Array1.t;
    var _byte_p:W8.t Array1.t;
    _byte_p <- witness;
    byte_p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- byte_p;
    _byte_p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux <@ SC.randombytes_1 (_byte_p);
    byte_p <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    aux_0 <- byte_p.[0];
    r <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <- (r `&` (W8.of_int 1));
    r <- aux_0;
    return (r);
  }
  
  proc bn_rsample_i (byte_z:W64.t Array32.t) : int * W64.t Array32.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_6: W64.t;
    var aux_7: W8.t Array256.t;
    var aux_0: W64.t Array32.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux <- 0;
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bn_set0 (byte_p);
    byte_p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_6) <- set0_64 ;
     _0 <- aux_5;
    cf <- aux_4;
     _1 <- aux_3;
     _2 <- aux_2;
     _3 <- aux_1;
     _4 <- aux_6;
    
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    while ((! cf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- byte_p;
      _byte_p <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_7 <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                   (WArray256.init64 (fun i_0 => _byte_p.[i_0]))
                                   i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux_7.[i_0])) i_0));
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ bn_copy (byte_p);
      byte_q <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_5, aux_0) <@ bn_subc (byte_q, byte_z);
      cf <- aux_5;
      byte_q <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + 1);
      i <- aux;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    }
    return (i, byte_p);
  }
  
  proc bn_rsample (byte_z:W64.t Array32.t) : W64.t Array32.t = {
    var aux_5: bool;
    var aux_4: bool;
    var aux_3: bool;
    var aux_2: bool;
    var aux_1: bool;
    var aux: int;
    var aux_6: W64.t;
    var aux_7: W8.t Array256.t;
    var aux_0: W64.t Array32.t;
    
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
    leakages <- LeakAddr([]) :: leakages;
    aux <- 0;
    i <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bn_set0 (byte_p);
    byte_p <- aux_0;
    leakages <- LeakAddr([]) :: leakages;
    (aux_5, aux_4, aux_3, aux_2, aux_1, aux_6) <- set0_64 ;
     _0 <- aux_5;
    cf <- aux_4;
     _1 <- aux_3;
     _2 <- aux_2;
     _3 <- aux_1;
     _4 <- aux_6;
    
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    while ((! cf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <- byte_p;
      _byte_p <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux_7 <@ SC.randombytes_256 ((Array256.init (fun i_0 => get8
                                   (WArray256.init64 (fun i_0 => _byte_p.[i_0]))
                                   i_0)));
      byte_p <-
      (Array32.init (fun i_0 => get64
      (WArray256.init8 (fun i_0 => aux_7.[i_0])) i_0));
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ bn_copy (byte_p);
      byte_q <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      (aux_5, aux_0) <@ bn_subc (byte_q, byte_z);
      cf <- aux_5;
      byte_q <- aux_0;
      leakages <- LeakAddr([]) :: leakages;
      aux <- (i + 1);
      i <- aux;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    }
    return (byte_p);
  }
  
  proc bn_lt_cf (a:W64.t Array32.t, b:W64.t Array32.t) : bool = {
    var aux_0: bool;
    var aux_1: int;
    var aux: W64.t;
    
    var cf:bool;
    var t:W64.t;
    var i:int;
    
    leakages <- LeakAddr([0]) :: leakages;
    aux <- a.[0];
    t <- aux;
    leakages <- LeakAddr([0]) :: leakages;
    (aux_0, aux) <- sbb_64 t b.[0] false;
    cf <- aux_0;
    t <- aux;
    leakages <- LeakFor(1,32) :: LeakAddr([]) :: leakages;
    i <- 1;
    while (i < 32) {
      leakages <- LeakAddr([i]) :: leakages;
      aux <- a.[i];
      t <- aux;
      leakages <- LeakAddr([i]) :: leakages;
      (aux_0, aux) <- sbb_64 t b.[i] cf;
      cf <- aux_0;
      t <- aux;
      i <- i + 1;
    }
    return (cf);
  }
  
  proc bn_rnd (a:W64.t Array32.t) : W64.t Array32.t = {
    var aux_0: W8.t Array256.t;
    var aux: W64.t Array32.t;
    
    var _byte_p:W64.t Array32.t;
    _byte_p <- witness;
    leakages <- LeakAddr([]) :: leakages;
    aux <- a;
    _byte_p <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ SC.randombytes_256 ((Array256.init (fun i => get8
                                 (WArray256.init64 (fun i => _byte_p.[i]))
                                 i)));
    a <-
    (Array32.init (fun i => get64 (WArray256.init8 (fun i => aux_0.[i])) i));
    return (a);
  }
  
  proc bn_rsample1 (a:W64.t Array32.t, bnd:W64.t Array32.t) : W64.t Array32.t = {
    var aux_0: bool;
    var aux: W64.t Array32.t;
    
    var cf:bool;
    
    leakages <- LeakAddr([]) :: leakages;
    aux <@ bn_rnd (a);
    a <- aux;
    leakages <- LeakAddr([]) :: leakages;
    aux_0 <@ bn_lt_cf (a, bnd);
    cf <- aux_0;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    while ((! cf)) {
      leakages <- LeakAddr([]) :: leakages;
      aux <@ bn_rnd (a);
      a <- aux;
      leakages <- LeakAddr([]) :: leakages;
      aux_0 <@ bn_lt_cf (a, bnd);
      cf <- aux_0;
    leakages <- LeakCond((! cf)) :: LeakAddr([]) :: leakages;
    
    }
    return (a);
  }
}.

