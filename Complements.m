// Extracted from Complements.tex by MagmaCode 2.1 on Tue Dec 26 11:02:42 2017
//
// Normaliser complements for the parabolic subgroups of finite unitary reflection groups
// Author: Don Taylor
// Created: 19 April 2017
// Revised: 12 July 2017

parabolicNames := [];
parabolicNames[4]  := [ "L1" ];
parabolicNames[5]  := [ "L1", "L1'" ];
parabolicNames[6]  := [ "A1", "L1" ];
parabolicNames[7]  := [ "A1", "L1", "L1'" ];
parabolicNames[8]  := [ "Z4" ];
parabolicNames[9]  := [ "A1", "Z4" ];
parabolicNames[10] := [ "Z4", "L1" ];
parabolicNames[11] := [ "Z4", "L1", "A1" ];
parabolicNames[12] := [ "A1" ];
parabolicNames[13] := [ "A1", "A1'" ];
parabolicNames[14] := [ "A1", "L1" ];
parabolicNames[15] := [ "A1", "A1'", "L1" ];
parabolicNames[16] := [ "Z5" ];
parabolicNames[17] := [ "A1", "Z5" ];
parabolicNames[18] := [ "L1", "Z5" ];
parabolicNames[19] := [ "Z5", "A1", "L1" ];
parabolicNames[20] := [ "L1" ];
parabolicNames[21] := [ "A1", "L1" ];
parabolicNames[22] := [ "A1" ];
parabolicNames[23] := [ "A1", "2A1", "A2", "I2(5)" ];
parabolicNames[24] := [ "A1", "A2", "B2" ];
parabolicNames[25] := [ "L1", "2L1", "L2" ];
parabolicNames[26] := [ "A1", "L1", "A1+L1", "L2", "G(3,1,2)" ];
parabolicNames[27] := [ "A1", "A2", "A2'", "I2(5)", "B2" ];
parabolicNames[28] := [ "A1", "A1'", "2A1", "A2", "A2'", "B2",
                        "A1+A2", "(A1+A2)'", "B3", "B3'" ];
parabolicNames[29] := [ "A1", "2A1", "A2", "B2", "A1+A2", "A3", "A3'",
                        "G(4,4,3)", "B3" ];
parabolicNames[30] := [ "A1", "2A1", "A2", "I2(5)", "A1+A2", "A1+I2(5)",
                        "A3", "H3" ];
parabolicNames[31] := [ "A1", "2A1", "A2", "G(4,2,2)", "A1+A2", "A3", "G(4,2,3)" ];
parabolicNames[32] := [ "L1", "2L1", "L2", "L1+L2", "L3" ];
parabolicNames[33] := [ "A1", "2A1", "A2", "A1+A2", "A3", "3A1", "G(3,3,3)",
                        "A1+A3", "A4", "G(3,3,4)", "D4" ];
parabolicNames[34] := [ "A1", "2A1", "A2", "A1+A2", "A3", "3A1", "G(3,3,3)",
                        "A1+A3", "G(3,3,4)", "A4", "2A1+A2", "2A2",
                        "A1+G(3,3,3)", "D4", "A1+A4", "A2+A3",
                        "A1+G(3,3,4)", "A5", "A5'", "D5", "G(3,3,5)", "K5" ];
parabolicNames[35] := [ "A1", "2A1", "A2", "A1+A2", "A3", "3A1", "A1+A3", "A4",
                        "2A2", "2A1+A2", "D4", "A1+A4", "D5", "A1+2A2", "A5" ];
parabolicNames[36] := [ "A1", "A2", "2A1", "A3", "A1+A2", "3A1", "3A1'", "A4",
                        "D4", "A1+A3", "(A1+A3)'", "2A2", "2A1+A2", "4A1",
                        "A5", "A5'", "D5", "A1+A4", "A1+D4", "A2+A3",
                        "2A1+A3", "A1+2A2", "3A1+A2", "A1+A2+A3", "A1+A5",
                        "A2+A4", "A1+D5", "A6", "E6", "D6"];
parabolicNames[37] := [ "A1", "2A1", "A2", "A1+A2", "3A1", "A3", "A1+A3", "2A2",
                        "A4", "2A1+A2", "D4", "4A1", "A1+A4", "A2+A3", "A5",
                        "D5", "A1+D4", "2A1+A3", "A1+2A2", "3A1+A2",
                        "A1+A5", "A2+A4", "A6", "2A1+A4", "E6", "A1+D5",
                        "2A3", "D6", "A2+D4", "A1+A2+A3", "2A1+2A2",
                        "A1+A6", "A1+A2+A4", "A1+E6", "A2+D5", "A3+A4",
                        "A7", "D7", "E7"];

AddAttribute(GrpPerm,"rootDatum");
rtDtmFormat := recformat< roots : SetIndx, coroots : SetIndx, rho : Map,
    W : GrpMat >;

Sxyz_3 := Sym(1);
Sxyz_3`rootDatum := [];

rootDatum := function(n)
  S := Sym(1);
  uggr := S`rootDatum;
  if IsDefined(uggr,n) then
     rtDtm := uggr[n];
     roots := rtDtm`roots;
     coroots := rtDtm`coroots;
     rho := rtDtm`rho;
     W := rtDtm`W;
  else
    roots, coroots, rho, W, J := ComplexRootDatum(n : NumFld);

    F := BaseRing(W);
    if F eq Rationals() then
      V := VectorSpace(F,Nrows(J),J);
    else
      sigma := map< F -> F | x :-> ComplexConjugate(x) >;
      V := UnitarySpace(J,sigma);
    end if;
    ChangeUniverse(~roots,V);
    ChangeUniverse(~coroots,V);
    rho := map< roots->coroots | a:->rho(a) >;
    S`rootDatum[n] := rec< rtDtmFormat |
      roots := roots, coroots := coroots, rho := rho, W := W >;
  end if;
  return roots, coroots, rho, W;
end function;

str := IntegerToString;

components := function(R)
  seq := [];
  X := R;
  while not IsEmpty(X) do
    r := X[1];
    Exclude(~X,r);
    C := [r];
    ndx := 0;
    while ndx lt #C do
      ndx +:= 1;
      a := C[ndx];
      extn := [ x : x in X | a*x ne x*a ];
      C cat:= extn;
      X := [ x : x in X | x notin extn ];
    end while;
    Append(~seq,C);
  end while;
  return seq;
end function;

maximalReps := function(refsubs)
  Sort(~refsubs, func< A,B | #B - #A >);
  if exists{ A : A in refsubs | not IsPrime(#A) } then
    R := [];
    for A in refsubs do
      if forall{ B : B in R | not A subset B } then
        Append(~R, A);
      end if;
    end for;
  else R := refsubs;
  end if;
  return [A.1 : A in R];
end function;

stabiliser := function(W,X)
  f,G,_ := OrbitAction(W,X);
  Psi := { f(x) : x in X };
  H := Stabiliser(G,Psi);
  return H @@ f;
end function;

orbits := function(G,T)
  orbs := [];
  while #T gt 0 do
    S := Rep(T)^G;
    Append(~orbs,S);
    T := { x : x in T | x notin S };
  end while;
  return orbs;
end function;

 groupName := AssociativeArray(car<Integers(),Integers(),Integers()>);
 groupName[<2,1,2>] := "A1";             // "SymmetricGroup"(2)
 groupName[<3,1,3>] := "L1";             // "CyclicGroup"(3)
 groupName[<4,1,4>] := "Z4";             // "CyclicGroup"(4)
 groupName[<5,1,5>] := "Z5";             // "CyclicGroup"(5)
 groupName[<6,1,6>] := "Z6";             // "CyclicGroup"(6)
 groupName[<6,3,2>] := "A2";             // "SymmetricGroup"(3)
 groupName[<8,1,8>] := "Z8";             // "CyclicGroup"(8)
 groupName[<8,4,2>] := "B2";             // "ShephardTodd"(2,1,2)
 groupName[<10,1,10>] := "Z10";          // "CyclicGroup"(10)
 groupName[<10,5,2>] := "I2(5)";         // "ShephardTodd"(5,5,2)
 groupName[<12,1,12>] := "Z12";          // "CyclicGroup"(12)
 groupName[<12,6,2>] := "I2(6)";         // "ShephardTodd"(6,6,2)
 groupName[<16,6,2>] := "G(4,2,2)";
 groupName[<16,8,2>] := "I2(8)";         // "ShephardTodd"(8,8,2)
 groupName[<18,5,3>] := "G(3,1,2)";
 groupName[<20,1,20>] := "Z20";          // "CyclicGroup"(20)
 groupName[<20,10,2>] := "I2(10)";       // "ShephardTodd"(10,10,2)
 groupName[<24,4,3>] := "L2";            // "ShephardTodd"(4)
 groupName[<24,1,24>] := "Z24";          // "CyclicGroup"(24)
 groupName[<24,6,2>] := "A3";            // "SymmetricGroup"(4)
 groupName[<24,8,2>] := "G(6,3,2)";
 groupName[<30,1,30>] := "Z30";          // "CyclicGroup"(30)
 groupName[<32,6,4>] := "G(4,1,2)";
 groupName[<32,10,2>] := "G(8,4,2)";
 groupName[<36,8,3>] := "G(6,2,2)";
 groupName[<48,9,2>] := "B3";            // "ShephardTodd"(2,1,3)
 groupName[<48,10,3>] := "G6";           // "ShephardTodd"(6)
 groupName[<48,12,2>] := "G12";          // "ShephardTodd"(12)
 groupName[<50,7,5>] := "G(5,1,2)";
 groupName[<54,9,2>] := "G(3,3,3)";
 groupName[<60,1,60>] := "Z60";          // "CyclicGroup"(60)
 groupName[<64,10,4>] := "G(8,2,2)";
 groupName[<72,8,3>] := "G5";            // "ShephardTodd"(5)
 groupName[<72,8,6>] := "G(6,1,2)";
 groupName[<96,6,4>] := "G8";            // "ShephardTodd"(8)
 groupName[<96,12,2>] := "G(4,4,3)";
 groupName[<96,18,2>] := "G13";          // "ShephardTodd"(13)
 groupName[<100,12,2>] := "G(10,2,2)";
 groupName[<120,10,2>] := "A4";          // "SymmetricGroup"(5)
 groupName[<120,15,2>] := "H3";          // "ShephardTodd"(23)
 groupName[<144,14,3>] := "G7";          // "ShephardTodd"(7)
 groupName[<144,20,3>] := "G14";         // "ShephardTodd"(14)
 groupName[<162,12,3>] := "G(3,1,3)";
 groupName[<192,12,2>] := "D4";          // "ShephardTodd"(2,2,4)
 groupName[<192,15,2>] := "G(4,2,3)";
 groupName[<192,18,4>] := "G9";          // "ShephardTodd"(9)
 groupName[<240,30,2>] := "G22";         // "ShephardTodd"(22)
 groupName[<288,14,4>] := "G10";         // "ShephardTodd"(10)
 groupName[<288,26,3>] := "G15";         // "ShephardTodd"(15)
 groupName[<336,21,2>] := "J3(4)";       // "ShephardTodd"(24)
 groupName[<360,20,3>] := "G20";         // "ShephardTodd"(20)
 groupName[<384,15,4>] := "G(4,1,3)";
 groupName[<384,16,2>] := "B4";          // "ShephardTodd"(2,1,4)
 groupName[<432,21,2>] := "G(6,3,3)";
 groupName[<576,26,4>] := "G11";         // "ShephardTodd"(11)
 groupName[<600,12,5>] := "G16";         // "ShephardTodd"(16)
 groupName[<648,12,3>] := "L3";          // "ShephardTodd"(25)
 groupName[<648,18,2>] := "G(3,3,4)";
 groupName[<720,15,2>] := "A5";          // "SymmetricGroup"(6)
 groupName[<720,50,3>] := "G21";         // "ShephardTodd"(21)
 groupName[<1152,24,2>] := "F4";         // "ShephardTodd"(28)
 groupName[<1200,42,5>] := "G17";        // "ShephardTodd"(17)
 groupName[<1296,21,3>] := "M3";         // "ShephardTodd"(26)
 groupName[<1536,24,2>] := "G(4,4,4)";
 groupName[<1800,32,5>] := "G18";        // "ShephardTodd"(18)
 groupName[<1920,20,2>] := "D5";         // "ShephardTodd"(2,2,5)
 groupName[<1944,22,3>] := "G(3,1,4)";
 groupName[<2160,45,2>] := "J3(5)";      // "ShephardTodd"(27)
 groupName[<3072,28,2>] := "G(4,2,4)";
 groupName[<3600,62,5>] := "G19";        // "ShephardTodd"(19)
 groupName[<3840,25,2>] := "B5";         // "ShephardTodd"(2,1,5)
 groupName[<5040,21,2>] := "A6";         // "SymmetricGroup"(7)
 groupName[<7680,40,2>] := "N4";         // "ShephardTodd"(29)
 groupName[<9720,30,2>] := "G(3,3,5)";
 groupName[<14400,60,2>] := "H4";        // "ShephardTodd"(30)
 groupName[<23040,30,2>] := "D6";        // "ShephardTodd"(2,2,6)
 groupName[<40320,28,2>] := "A7";        // "SymmetricGroup"(8)
 groupName[<46080,36,2>] := "B6";        // "ShephardTodd"(2,1,6)
 groupName[<46080,60,2>] := "O4";        // "ShephardTodd"(31)
 groupName[<51840,36,2>] := "E6";        // "ShephardTodd"(35)
 groupName[<51840,45,2>] := "K5";        // "ShephardTodd"(33)
 groupName[<155520,40,3>] := "L4";       // "ShephardTodd"(32)
 groupName[<174960,45,2>] := "G(3,3,6)";
 groupName[<322560,42,2>] := "D7";       // "ShephardTodd"(2,2,7)
 groupName[<362880,36,2>] := "A8";       // "SymmetricGroup"(9)
 groupName[<2903040,63,2>] := "E7";      // "ShephardTodd"(36)
 groupName[<5160960,56,2>] := "D8";      // "ShephardTodd"(2,2,8)
 groupName[<39191040,126,2>] := "K6";    // "ShephardTodd"(34)
 groupName[<696729600,120,2>] := "E8";   // "ShephardTodd"(37)

name := func< n, r, m |
  IsDefined(groupName,<n,r,m>) select groupName[<n,r,m>]
    else "<"*str(n)*"|"*str(r)*"|"*str(m)*">" >;

prettyName := function(names)
  if IsEmpty(names) then return "*X*"; end if;
  count := func< n | (n gt 1) select IntegerToString(n) else "" >;
  Sort(~names);
  sep := "";
  name := "";
  prev_tag := names[1];
  tag_num := 0;
  for tag in names do
    if tag eq prev_tag then tag_num +:= 1;
    else
      name *:= sep * count(tag_num) * prev_tag;
      prev_tag := tag;
      tag_num := 1;
      sep := "+";
    end if;
  end for;
  name *:= sep * count(tag_num) * prev_tag;
  return name;
end function;

standardName1 := function(G,R)
  if IsEmpty(R) then return "A0"; end if;
  assert G eq sub< G | R >;
  sform := [];
  for C in components(R) do
    Append(~sform, name(Order(sub<G|C>),#C,Max({Order(r) : r in C})));
  end for;
  return prettyName(sform);
end function;

standardName2 := function(H,roots,rho)
  if #H eq 1 then return "A0"; end if;
  R_ := { sub< H | r > : a in roots | r in H where r is Reflection(a,rho(a)) };
  R := maximalReps(Setseq(R_));
  return standardName1(H,R);
end function;

rankTwo := function(n,X)
  roots, _, rho, W := rootDatum(n);
  V := Universe(roots);

  H := sub<W|>;
  Xi := [];

  Delta := roots[1..Ngens(W)];
  case n:
    when 4: F<omega> := BaseRing(W);
      J := case< X | "L1": 1, default: 0>;
      Xi := [Delta[1],-Delta[1]];
    when 5: F<omega> := BaseRing(W);
      J := case< X | "L1": 1, "L1'": 2, default: 0>;
      Xi := case< X |
        "L1": [ g*Delta[1] : g in [1,-1]],
        "L1'": [ g*Delta[2] : g in [1,-1]],
         default: []>;
    when 6: F<i,omega> := BaseRing(W);
      J := case< X | "A1": 1, "L1": 2, default: 0>;
      if X eq "L1" then
        Xi := [ g*Delta[2] : g in [1,-1,i,-i]];
      elif X eq "A1" then
        H := sub< W| [-i,0, -2*i*omega - i + 1,i]>;
      end if;
    when 7: F<i,omega> := BaseRing(W);
      J := case< X | "A1": 1, "L1": 2, "L1'": 3, default: 0>;
      Xi := case< X |
        "L1": [ g*Delta[2] : g in [1,-1,i,-i]],
        "L1'": [ g*Delta[3] : g in [1,-1,i,-i]],
         default: []>;
      if X eq "A1" then
        H := sub< W|[-i*omega + 1,i*omega, -2*i*omega + 2,i*omega - 1]>;
      end if;
    when 8: F<i> := BaseRing(W);
      J := case< X | "Z4": 1, default: 0>;
      Xi := case< X | "Z4": [V| Delta[1]], default: []>;
    when 9: F<i,a> := BaseRing(W);
      J := case< X | "A1": 1, "Z4": 2, default: 0>;
      H := case< X |
        "A1": sub< W| [(i+1)*a/2,0, 0,(i+1)*a/2] >,
        "Z4": sub< W| [i*a/2 + a/2,1, 0,-i*a/2 + a/2] >,
         default: sub<W|>>;
    when 10: F<i,omega> := BaseRing(W);
      J := case< X | "Z4": 1, "L1": 2, default: 0>;
      Xi := case< X |
        "Z4": [ g*Delta[1] : g in [1,omega,omega^2]],
        "L1": [ g*Delta[2] : g in [1,-1,i,-i]],
         default: []>;
    when 11: F<i,omega,a> := BaseRing(W);
      J := case< X | "Z4": 1, "A1": 2, "L1": 3, default: 0>;
      Xi := case< X |
        "L1": [ g^j*Delta[3] : j in [0..7] | true where g is (1-i)/a ],
         default: []>;
      H := case< X |
        "Z4": sub< W| [(i-1)*omega*a/2,0, i*omega*(a+1),-(i+1)*omega*a/2]>,
        "A1": sub< W| [(i+1)*omega*a/2,0, 0, (i+1)*omega*a/2]>,
         default: sub<W|>>;
    when 12: F<b> := BaseRing(W);
      J := case< X | "A1": 1, default: 0>;
      Xi := case< X | "A1": [V| Delta[1]], default: []>;
    when 13: F<i,a> := BaseRing(W);
      J := case< X | "A1": 1, "A1'": 2, default: 0>;
      H := case< X |
        "A1": sub< W| [ (i-1)*a/2,0, i*(a+1), -(i+1)*a/2 ] >,
        "A1'": sub< W| [ (i+1)*a/2+1,-1, (i+1)*(a+1)+1, -(i+1)*a/2-1 ]>,
         default: sub<W|>>;
    when 14: F<b,omega> := BaseRing(W);
      J := case< X | "L1": 1, "A1": 2, default: 0>;
      Xi := case< X |
        "L1": [Delta[1],-Delta[1]],
        "A1": [ g*Delta[2] : g in [1,omega,omega^2]],
         default: []>;
    when 15: F<i,omega,a> := BaseRing(W);
      J := case< X | "A1": 1, "L1": 2, "A1'": 3, default: 0>;
      Xi := case< X |
        "L1": [ g*Delta[2] : g in [1,-1,i,-i]],
         default: []>;
      H := case< X |
        "A1": sub< W| [ (i+1)*omega*a/2,0, i*omega*(a+1),-(i-1)*omega*a/2 ]>,
        "A1'": sub< W| [ -i*omega*(a+1),i*omega, -2*i*omega*(a+1),i*omega*(a+1) ] >,
         default: sub<W|>>;
    when 16: F<z5> := BaseRing(W);
      J := case< X | "Z5": 1, default: 0>;
      Xi := case< X |
        "Z5": [ g*Delta[1] : g in [1,-1]],
         default: []>;
    when 17: F<i,z5> := BaseRing(W);
      J := case< X | "A1": 1, "Z5": 2, default: 0>;
      Xi := case< X |
        "Z5": [ i^j*Delta[2] : j in [0..3]],
         default: []>;
      if X eq "A1" then
        H := sub< W| [i*z5^3,0, -i*z5 + i + z5^3,-i*z5^3] >;
      end if;
    when 18: F<omega,z5> := BaseRing(W);
      J := case< X | "L1": 1, "Z5": 2, default: 0>;
      Xi := case< X |
        "L1": [ (-z5)^j*Delta[1] : j in [0..9]],
        "Z5": [ (-omega)^j*Delta[2] : j in [0..5]],
         default: []>;
    when 19: F<i,omega,z5> := BaseRing(W);
      J := case< X | "Z5": 1, "L1": 2, "A1": 3,  default: 0>;
      Xi := case< X |
        "Z5": [ (-i*omega)^j*Delta[1] : j in [0..11]],
        "L1": [ (i*z5)^j*Delta[2] : j in [0..19]],
         default: []>;
      if X eq "A1" then
        H := sub< W| [omega^2-z5,z5, omega*(z5^2+z5-1)-z5-2,-omega^2+z5] >;
      end if;
    when 20: F<omega,tau> := BaseRing(W);
      J := case< X | "L1": 1, default: 0>;
      Xi := case< X |
        "L1": [ Delta[1], -Delta[1] ],
         default: []>;
    when 21: F<i,omega,tau> := BaseRing(W);
      J := case< X | "A1" :1, "L1": 2, default: 0>;
      Xi := case< X |
        "L1": [ i^j*Delta[2] : j in [0..3]],
         default: []>;
      if X eq "A1" then
        H := sub< W| [-i*omega,0, -i*omega^2+i-omega*tau,i*omega] >;
      end if;
    when 22: F<i,tau> := BaseRing(W);
      J := case< X | "A1": 1, default: 0>;
      if X eq "A1" then
        H := sub< W| [i,0, i*tau-i+1,-i] >;
      end if;
    else
      error "G" * str(n), "is not rank 2";
  end case;
  error if J eq 0, "Invalid parabolic name";
  P := sub< W | W.J >;
  N := Normaliser(W,P);
  Q := Stabiliser(N,Delta[J]);
  if Xi eq [] then Xi := [Delta[J]]; end if;
  if #H eq 1 then H := stabiliser(W,Set(Xi)); end if;
  return P,Q,H,N,roots,rho,J,Xi,W;
end function;

eisensteinType := function(n,X)
  roots, _, rho, W := rootDatum(n);
  V := Universe(roots);
  Delta := Basis(V);
  if n eq 27 then
    F<omega,tau> := BaseRing(W);
  else
    F<omega> := BaseRing(W);
  end if;
  thicken := func< J | J cat [ omega*v : v in J] cat [omega^2*v : v in J ] >;
  Xi := [];
  case n:
    when 25:
      gens := [W.1,W.2,W.3];
      J := case< X |
        "L1": [1],
        "2L1": [1,3],
        "L2": [1,2],
        default : []>;
      Xi := case< X |
        "L1": [V| [1,0,0], [-1,0,0]],
        "2L1" : [V| [1,0,0], [-1,0,0], [0,0,1], [0,0,-1]],
         default : [] >;
    when 26:
      gens := [W.1,W.2,W.3];
      J := case< X |
        "L1": [1],
        "A1": [3],
        "A1+L1": [1,3],
        "L2": [1,2],
        "G(3,1,2)": [2,3],
        default : []>;
      Xi := case< X |
        "L1": [V| [1,0,0], [-1,0,0]],
        "A1+L1": [V| [1,0,0], [-1,0,0], [0,0,1],[0,0,omega],[0,0,omega^2]],
        "G(3,1,2)": [V| [0,1,0], [0,-1,0], [0,0,1], [0,0,-1]],
         default : [] >;
    when 27:
      Delta cat:= [V| [1,-1,0]];
      gens := [W.1,W.2,W.3,W.1*W.2*W.1];
      J := case< X |
        "A1": [1],
        "A2": [1,2],
        "A2'": [3,4],
        "I2(5)": [1,3],
        "B2": [2,3],
         default : []>;
      Xi := case< X |
        "A2" : [V|
          [1, 0, 0], [omega, 0, 0], [omega^2, 0, 0],
          [0, -1, 0], [0, -omega, 0], [0, -omega^2, 0]],
        "A2'" : [V|
          [0, 0, 1], [0, 0, omega], [0, 0, omega^2],
          [-1, 1, 0], [-omega,omega,0], [-omega^2,omega^2,0]],
         default : [] >;
    when 32:
      gens := [W.1,W.2,W.3,W.4];
      J := case< X |
        "L1": [1],
        "L2": [1,2],
        "2L1": [1,3],
        "L3":[1,2,3],
        "L1+L2":[1,2,4],
        default : []>;
      Xi := case< X |
        "L1": [V| [1,0,0,0], [-1,0,0,0]],
        "2L1" : [V| [1,0,0,0], [-1,0,0,0], [0,0,1,0], [0,0,-1,0]],
        "L3": [V|
          [1, 0, 0, 0], [-1, 0, 0, 0],
          [0, omega^2, 0, 0], [0,-omega^2, 0, 0],
          [0, 0, omega, 0], [0, 0,-omega, 0]],
        "L1+L2": [V|
          [1, 0, 0, 0], [omega, 0, 0, 0], [omega^2, 0, 0, 0],
          [0,-1, 0, 0], [0,-omega, 0, 0], [0,-omega^2, 0, 0],
          [0, 0, 0, 1], [0, 0, 0,-1]],
         default : [] >;
    when 33:
      Delta cat:= [V![-1,-1,-1,0,0]];
      ss := W.1*W.2*W.1;
      gens := [ W.i : i in [1..5]];
      Append(~gens, ss*W.3*ss);
      J := case< X |
        "A1": [1],
        "2A1": [1,3],
        "A2": [1,2],
        "A1+A2": [1,2,5],
        "A3": [1,2,3],
        "3A1": [1,3,5],
        "G(3,3,3)": [2,3,4],
        "A1+A3": [1,2,3,5],
        "A4": [1,2,4,5],
        "G(3,3,4)": [1,2,3,4],
        "D4": [2,4,5,6],
         default : [] >;
      Xi := case< X |
        "G(3,3,3)": [V|
          [0, 1, 0, 0, 0],
          [0, 0, 1, 0, 0],
          [0, 0, 0, omega^2, 0],
          [0, 1, 1, -omega^2, 0],
          [0, 1, -omega^2, omega, 0],
          [0, -omega, 1, 1, 0],
          [0, 0, -omega, -omega, 0],
          [0, -omega^2, 0, -1, 0]],
        "G(3,3,4)" : [V|
          [1, 0, 0, 0, 0],
          [0, 1, 0, 0, 0],
          [0, 0, 1, 0, 0],
          [0, 0,-1, 0, 0],
          [0, 0, 0, 1, 0],
          [0, 0, 0,-1, 0],
          [-1, -1, 0, 0, 0]],
         default : [] >;
    when 34:
      Delta cat:= [V![-1,-1,-1,0,0,0]];
      ss := W.1*W.2*W.1;
      gens := [ W.i : i in [1..6]];
      Append(~gens, ss*W.3*ss);
      J := case< X |
        "A1": [1],
        "2A1": [1,3],
        "A2": [1,2],
        "A1+A2": [1,2,5],
        "A3": [1,2,3],
        "3A1": [1,3,5],
        "G(3,3,3)": [2,3,4], // *
        "A1+A3": [1,2,3,5],
        "G(3,3,4)": [1,2,3,4],
        "A4": [1,2,4,5],
        "2A1+A2": [1,3,5,6],
        "2A2": [1,2,5,6],
        "A1+G(3,3,3)": [2,3,4,6], // *
        "D4": [2,4,5,7],
        "A1+A4": [1,3,4,5,6],
        "K5": [1,2,3,4,5],
        "A5": [1,2,4,5,6],
        "A5'": [1,4,5,6,7],
        "A1+G(3,3,4)": [1,2,3,4,6], // *
        "D5": [2,4,5,6,7],
        "A2+A3": [1,2,3,5,6],
        "G(3,3,5)": [2,3,4,5,6], // *
         default : [] >;
      Xi := case< X |
        "G(3,3,3)": [V|
          [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,omega^2,0,0],
          [0,1,1,-omega^2,0,0], [0,1,-omega^2,omega,0,0],
          [0,-omega,1,1,0,0], [0,0,-omega,-omega,0,0], [0,-omega^2,0,-1,0,0]],
        "G(3,3,4)" : [V|
          [0,1,0,0,0,0], [-1,-1,0,0,0,0], [0,0,0,1,0,0], [0,0,0,-1,0,0],
          [0,0,omega^2,0,0,0], [0,0,-omega^2,0,0,0], [0,0,omega,omega,0,0],
          [0,0,-omega,-omega,0,0]],
        "G(3,3,5)": [V|
          [0,omega^2,0,0,0,0], [0,0,1,0,0,0], [0,0,0,0,1,0], [0,-omega,-omega,0,0,0],
          [0,-omega,0,-omega^2,0,0], [0,1,1,-omega^2,0,0], [0,0,-omega^2,-omega^2,0,0],
          [0,0,0,-omega,-omega,-omega]],
        "A1+G(3,3,3)": [V|
          [0,1,0,0,0,0], [0,0,1,0,0,0], [0,0,0,omega^2,0,0],
          [0,1,1,-omega^2,0,0], [0,1,-omega^2,omega,0,0],
          [0,-omega,1,1,0,0], [0,0,-omega,-omega,0,0], [0,-omega^2,0,-1,0,0],
          [0,0,0,0,0,1], [0,0,0,0,0,omega], [0,0,0,0,0,omega^2]],
        "A1+G(3,3,4)": [V|
          [0,1,0,0,0,0], [-1,-1,0,0,0,0], [0,0,0,1,0,0], [0,0,0,-1,0,0],
          [0,0,omega^2,0,0,0], [0,0,-omega^2,0,0,0], [0,0,omega,omega,0,0],
          [0,0,-omega,-omega,0,0],
          [0,0,0,0,0,1], [0,0,0,0,0,omega], [0,0,0,0,0,omega^2]],
         default : [] >;
    else
      error "G" * str(n), "is not Eisenstein";
  end case;
  error if IsEmpty(J), "Invalid parabolic name";
  P := sub< W | [gens[i] : i in J ]>;
  if IsEmpty(Xi) then Xi := thicken([Delta[j] : j in J]); end if;
  N := Normaliser(W,P);
  Q := Stabiliser(N,[Delta[j] : j in J]);
  H := stabiliser(W,Set(Xi));
  return P,Q,H,N,roots,rho,J,Xi,W;
end function;

euclidType := function(n,X)
    roots, _, rho, W := rootDatum(n);
    V := Universe(roots);
    Delta := Basis(V);
    Xi := [];
    case n:
      when 23:
        J := case< X |
          "A1" : [1],
          "2A1": [1,3],
          "A2": [2,3],
          "I2(5)": [1,2],
           default : [] >;
      when 24:
        J := case< X |
          "A1": [1],
          "A2": [1,2],
          "B2": [1,3],
           default : []>;
         Xi := case< X |
          "A2" : [V| [1,0,0], [0,-1,0]],
           default : []>;
      when 28:
        J := case< X |
          "A1": [1],
          "A1'": [3],
          "A2": [1,2],
          "2A1": [1,3],
          "A2'": [3,4],
          "B2": [2,3],
          "B3": [2,3,4],
          "B3'": [1,2,3],
          "A1+A2": [1,3,4],
          "(A1+A2)'": [1,2,4],
           default : [] >;
      when 30:
        J := case< X |
          "A1": [1],
          "2A1": [1,3],
          "I2(5)": [1,2],
          "A2": [3,4],
          "A1+I2(5)": [1,2,4],
          "A3": [2,3,4],
          "H3": [1,2,3],
          "A1+A2": [1,3,4],
           default : [] >;
      when 35:
        J := case< X |
          "A1": [1],
          "2A1": [1,2],
          "A2": [1,3],
          "A1+A2": [1,2,3],
          "A3": [1,3,4],
          "3A1": [1,2,6],
          "A1+A3": [1,3,4,6],
          "A4": [1,2,3,4],
          "2A2": [1,3,5,6],
          "2A1+A2": [1,2,5,6],
          "D4": [2,3,4,5],
          "A5": [1,3,4,5,6],
          "A1+A4": [1,2,3,4,6],
          "D5": [1,2,3,4,5],
          "A1+2A2": [1,2,3,5,6],
           default : [] >;
      when 36:
        J := case< X |
          "A1": [1],
          "2A1": [1,2],
          "A2": [1,3],
          "A1+A2": [1,2,3],
          "A3": [1,3,4],
          "3A1": [1,2,6],
          "3A1'": [2,5,7],
          "A1+A3": [1,3,4,6],
          "(A1+A3)'": [2,5,6,7],
          "A4": [1,2,3,4],
          "2A2": [1,3,5,6],
          "2A1+A2": [1,2,5,6],
          "D4": [2,3,4,5],
          "4A1": [1,2,5,7],
          "A5": [1,3,4,5,6],
          "A5'": [2,4,5,6,7],
          "A1+A4": [1,2,3,4,6],
          "D5": [1,2,3,4,5],
          "2A1+A2": [1,2,3,5,6],
          "A2+A3": [1,3,5,6,7],
          "2A1+A3": [1,2,5,6,7],
          "A1+2A2": [1,2,3,6,7],
          "A1+D4": [2,3,4,5,7],
          "3A1+A2": [1,2,3,5,7],
          "A1+D5": [1,2,3,4,5,7],
          "A1+A5": [1,2,4,5,6,7],
          "A2+A4": [1,2,3,4,6,7],
          "A1+A2+A3": [1,2,3,5,6,7],
          "A6": [1,3,4,5,6,7],
          "D6": [2,3,4,5,6,7],
          "E6": [1,2,3,4,5,6],
           default : [] >;
      when 37:
        J := case< X |
          "A1": [1],
          "2A1": [1,2],
          "A2": [1,3],
          "A1+A2": [1,2,3],
          "3A1": [1,2,6],
          "A3": [1,3,4],
          "A1+A3": [1,3,4,6],
          "2A2": [1,3,5,6],
          "A4": [1,2,3,4],
          "2A1+A2": [1,2,5,6],
          "D4": [2,3,4,5],
          "4A1": [1,2,5,7],
          "A1+A4": [1,2,3,4,6],
          "A2+A3": [1,3,5,6,7],
          "A5": [1,3,4,5,6],
          "D5": [1,2,3,4,5],
          "A1+D4": [2,3,4,5,7],
          "2A1+A3": [1,2,5,6,7],
          "A1+2A2": [1,2,3,5,6],
          "3A1+A2": [1,2,3,5,7],
          "A1+A5": [1,2,4,5,6,7],
          "A2+A4": [1,2,3,4,6,7],
          "A6": [1,3,4,5,6,7],
          "2A1+A4": [1,2,5,6,7,8],
          "E6": [1,2,3,4,5,6],
          "A1+D5": [1,2,3,4,5,7],
          "2A3": [1,3,4,6,7,8],
          "D6": [2,3,4,5,6,7],
          "A2+D4": [2,3,4,5,7,8],
          "A1+A2+A3": [1,2,3,5,6,7],
          "2A1+2A2": [1,2,3,5,7,8],
          "A1+A6": [1,2,4,5,6,7,8],
          "A1+A2+A4": [1,2,3,5,6,7,8],
          "A1+E6": [1,2,3,4,5,6,8],
          "A2+D5": [1,2,3,4,5,7,8],
          "A3+A4": [1,2,3,4,6,7,8],
          "A7": [1,3,4,5,6,7,8],
          "D7": [2,3,4,5,6,7,8],
          "E7": [1,2,3,4,5,6,7],
           default : [] >;
      else
        error "G" * str(n), "is not Euclidean";
    end case;
    error if IsEmpty(J), "Invalid parabolic name",X;
    P := sub< W | [W.i : i in J ]>;
    if IsEmpty(Xi) then Xi := [Delta[j] : j in J]; end if;
    N := Normaliser(W,P);
    Q := Stabiliser(N,Xi);
    H := stabiliser(W,Set(Xi));
    return P,Q,H,N,roots,rho,J,Xi,W;
end function;

gaussType := function(n,X)
    roots, _, rho, W := rootDatum(n);
    V := Universe(roots);
    Delta := Basis(V);
    F<i> := BaseRing(W);
    Xi := [];
    case n:
      when 29:
        gens := [W.1,W.2,W.3,W.4,W.1*W.2*W.1];
        Delta cat:= [V![1,1,0,0]];
        J := case< X |
          "A1" : [1], // Q not in H, so H is not a stabiliser
          "A2" : [1,2],
          "B2" : [2,3],
          "2A1" : [1,4], // Q not in H, so H is not a stabiliser
          "A1+A2" : [1,2,4], // Q = 1 but H is not a stabiliser
          "A3" : [1,3,4],
          "A3'" : [3,4,5],
          "B3" : [2,3,4], // Q not in H, so H is not a stabiliser
          "G(4,4,3)" : [1,2,3],
          default : []>;
        Xi := case< X |
          "A2" : [V|
            [ 1, 0, 0, 0], [-1, 0, 0, 0], [0, i, 0, 0], [0,-i, 0, 0]],
          "B2" : [V|
            [0, i, i - 1, 0], [0, 0, 1, 0], [0, 1, 0, 0], [0, -i - 1, -i, 0]],
          "A3" : [V|
            [ i, 0, 0, 0], [-i, 0, 0, 0], [ 0, 0, 1, 0], [ 0, 0,-1, 0],
            [ 0, 0, i, 0], [ 0, 0,-i, 0], [ 0, 0, 0, i], [ 0, 0, 0,-i]],
          "A3'" : [V|
            [ 0, 0, 0, i], [ 0, 0, 0,-i], [ 0, 0, 1, 0], [ 0, 0,-1, 0],
            [ 0, 0, i, 0], [ 0, 0,-i, 0], [ 1, 1, 0, 0], [-1,-1, 0, 0]],
         "G(4,4,3)" : [V|
            [ 0, 0, i, 0], [ 0, 0,-i, 0], [ i, 0, 1, 0], [-i, 0,-1, 0],
            [ 0, i, i - 1, 0], [ 0,-i,-i+1, 0], [ i, 1, i+1, 0], [-i,-1,-i-1, 0]],
          default : []>;
        H := case< X |
          "A1": sub< W |

            [1,0,0,0, i,2,i+2,i+1, -i,-1,-i-1,-i-1, -1, i,2*i-1,i],
            [1,0,0,0, -i,-i-1,-2*i-1,-i, 0,0,1,0, i,i+2,2*i+1,i+1],
            [-1,0,0,0, 0,i,i-1,0, 0,-i-1,-i,0, i+1,2,2,1],
            [i,0,0,0, 0,i,0,0, 0,0,i,0, 0,0,0,i]>,
          "2A1" : sub< W |
            [0,0,0,i, i,1,i+2,1, 0,0,-1,0, -i,0,0,0],
            [0,0,0,-1, -i,-i-2,-2*i-1,-i, i+1,2,i+2,i+1, -1,0,0, 0],
            [-1,0,0,0, -1,2*i-1,2*i-2,i-1, 1,-2*i,-2*i+1,-i, 0,0,0,1]>,
          "A1+A2" : sub< W | [i,0,0,0, 0,i,0,0, 0,0,i,0, 0,0,0,i]>,
          "B3" : sub< W | [i,0,0,0, 0,i,0,0, 0,0,i,0, 0,0,0,i]>,
           default : sub<W|> >;
      when 31:
        gens := [W.1,W.2,W.3,W.4,W.5];
        Delta cat:= [V![1,0,-i,0]];
        J := case< X |
          "A1" : [1], // Q not in H
          "2A1" : [1,4], // Q not in H
          "A2" : [1,2],
          "G(4,2,2)" : [1,3,5], // Q not in H
          "A3" : [2,3,4],
          "A1+A2" : [1,2,4], // H is not a stabiliser
          "G(4,2,3)" : [1,2,3,5], // Q not in H
          default : []>;
        Xi := case< X |
          "A2" : [V|
            [1, 0, 0, 0], [-1, 0, 0, 0], [0, i, 0, 0], [0, -i, 0, 0]],
          "A3" : [V|
            [0, 1, 0, 0], [0,-1, 0, 0],
            [0, 0, 1, 0], [0, 0,-1, 0], [0, 0, i, 0], [0, 0,-i, 0],
            [0, 0, 0, 1], [0, 0, 0,-1]],
          default : []>;
        H := case< X |
          "A1" : sub< W |
            [1,0,0,0, 0,1,0,0, 0,0,1,1, 0,0,0,-1],
            [1,0,0,0, i-1,-1,-i+1,0, 0,0,1,0, -1,-i-1,1,1],
            [i,0,0,0, -2*i-1,-i,2*i,i, 1,0,-1,0, 0,0,0,-1]>,
          "2A1" : sub< W |
            [0,0,0,i, -2,-i-1,i+2,1, -1,-i,i+1,i+1, -i,0,0,0],
            [1,0,0,0, -i+1,1,-2,-1, 1,0,-i,-i, 0,0,0,i]>,
          "G(4,2,2)" : sub< W |
            [-1,0,0,0, 0,-i,1,1, i,0,-i,0, -1,0,i+1,1],
            [-i,0,-1,0, i+1,0,-i,-i, 0,0,-1,0, i-1,-1,-i+2,-i+1]>,
          "A1+A2" : sub< W | [i,0,0,0, 0,i,0,0, 0,0,i,0, 0,0,0,i]>,
          "G(4,2,3)" : sub< W | [i,0,0,0, 0,i,0,0, 0,0,i,0, 0,0,0,i]>,
          default : sub<W|> >;
    else
      error "G" * str(n), "is not Gaussian";
    end case;
    error if IsEmpty(J), "Invalid parabolic name";
    P := sub< W | [gens[i] : i in J ]>;
    if IsEmpty(Xi) then
      Xi := [V| Delta[j] : j in J];
    end if;
    N := Normaliser(W,P);
    Q := Stabiliser(N,Xi);
    if #H eq 1 then H := stabiliser(W,Set(Xi)); end if;
    return P,Q,H,N,roots,rho,J,Xi,W;
end function;

paraData := function(n,X)
  if n in [4..22] then
    return rankTwo(n,X);
  elif n in [29,31] then
    return gaussType(n,X);
  elif n in [23,24,28,30,35,36,37] then
    return euclidType(n,X);
  elif n in [25,26,27,32,33,34] then
    return eisensteinType(n,X);
  else error "Shephard-Todd index",n,"is out of range";
  end if;
end function;

restriction := func< M, S | Solution(T,T*M) where T is Matrix(S) >;

restrictGroup := function(G,S)
  T := Matrix(S);
  n := Nrows(T);
  F := BaseRing(T);
  return sub<GL(n,F) | [ restriction(G.i,S) : i in [1..Ngens(G)]] >;
end function;

reflectionPart := function(P,K,V)
  E := sub< V| Basis(&meet[ Eigenspace(r,1) : r in Generators(P)]) >;
  L := restrictGroup(K,Basis(E));
  R_ := Setseq({ sub<L|r> : r in L | IsReflection(r) });
  R := maximalReps(R_);
  return sub< L | R >, E, R;
end function;

display := procedure(n : headings := false)
  if headings then
    printf "\n%3o %8o %10o %10o %12o %10o %6o\n",
      "G"*IntegerToString(n),"P","Q","|H0|","H0","H=H0","a";
    print "         ",&*["-" : i in [1..56]];
  end if;
  for X in parabolicNames[n] do
    P,Q,H,N,roots,rho,J,Xi,W := paraData(n,X);
    V := Universe(roots);
    H0, E, R := reflectionPart(P,N,V);
    a := Index(H,Centraliser(H,P));
    printf "%12o %10o %10o %12o %10o %6o\n",
      X,standardName2(Q,roots,rho), #H0,standardName1(H0,R),#H eq #H0,a;
  end for;
end procedure;

checkRoots := procedure()
  for n := 4 to 37 do
    roots,coroots,rho,W,J := ComplexRootDatum(n : NumFld);
    V := Universe(roots);
    for i := 1 to Ngens(W) do
      a := roots[i];
      b := a*W.i;
      assert sub<V|a> eq sub<V|b> and a ne b;
    end for;
  end for;
  "Test passed!";
end procedure;

nameCheck := procedure()
  for n := 4 to 37 do
    passed := true;
    for X in parabolicNames[n] do
      P,Q,H,N,roots,rho := paraData(n,X);
      N := standardName2(P,roots,rho);
      if X ne N then
        print "Possible name error:",X,N,"in group",n;
        passed := false;
      end if;
    end for;
    if passed then "Group",n,"passed"; end if;
  end for;
end procedure;

checkComplement := procedure(n,X)
  P,Q,H,N,roots,rho,J,Xi,W := paraData(n,X);
  "P meet H = 1    :",P meet H eq sub<P|>;
  "N eq <P,H>      :", N eq sub<N | P,H >;
  "generation of P :",P eq sub<P| [Reflection(a,rho(a)) : a in Xi] >;
end procedure;

standardParabolic := function(m,p,n0,lambda)
  n := n0 + &+lambda;
  W := ShephardTodd(m,p,n);
  Sort(~lambda);

  K := [ i eq 1 select 0 else Self(i-1) + lambda[i-1] : i in [1..#lambda+1] ];
  gens := [ W.i : i in &cat [[K[j-1]+1 .. K[j]-1] : j in [2..#K]] ];
  if n0 eq 1 then
    Append(~gens, W.Ngens(W) );
  elif n0 gt 1 then
    gens cat:= [ W.i : i in [K[#K] + 1 .. Ngens(W)] ];
  end if;
  return sub<W | gens>;
end function;

indexForm := func<lambda |
  [ < i, m > : i in [1..&+lambda] | m ne 0 where m is #[x : x in lambda | x eq i]] >;

stdRefCompGens := function(m,p,n0,lambda)
  n := n0 + &+lambda;
  ndx := indexForm(lambda);
  W := ShephardTodd(m,p,n);
  if m le 2 then F := Rationals(); theta := -1;
  else F<theta> := CyclotomicField(m); end if;
  t := IdentityMatrix(F,n);
  if n0 ne 0 then
    t[n,n] := theta^-1;
  end if;
  gseq := [];
  ptr := 0;
  for pair in ndx do
    k, b_k := Explode(pair);
    p_k := (p ne 1 and n0 eq 0) select p div GCD(p,k) else 1;
    G := ChangeRing(ShephardTodd(m,p_k,b_k),F);
    id1 := IdentityMatrix(F,ptr);
    id_k := IdentityMatrix(F,k);
    ptr +:= k*b_k;
    id2 := IdentityMatrix(F,n-ptr);
    if n0 ne 0 then
      gens := [W| DiagonalJoin(<id1,TensorProduct(G.i,id_k),id2>) :
        i in [1..Ngens(G)-1]];
      g := DiagonalJoin(<id1,TensorProduct(G.b_k,id_k),id2>) * t^k;
      Append(~gens,W!g);
    else
      gens := [W| DiagonalJoin(<id1,TensorProduct(G.i,id_k),id2>) :
        i in [1..Ngens(G)]];
    end if;
    Append(~gseq,gens);
  end for;
  return gseq;
end function;

baseGroup := function(m,p,n)
  if m le 2 then F := Rationals(); theta := -1;
  else F<theta> := CyclotomicField(m); end if;
  gens := [];
  if p eq 1 then
    for j := 1 to n do
      M := IdentityMatrix(F,n);
      M[j,j] := theta;
      Append(~gens,M);
    end for;
  else
    for j := 1 to n-1 do
      M := IdentityMatrix(F,n);
      M[j,j] := theta;
      M[j+1,j+1] := theta^-1;
      Append(~gens,M);
    end for;
    if p ne m then
      M := IdentityMatrix(F,n);
      M[1,1] := theta^p;
      Append(~gens,M);
    end if;
  end if;
  return sub<GL(n,F) | gens>;
end function;

diagPart := function(m,lambda)
  n := &+lambda;
  ndx := indexForm(lambda);
  if m le 2 then F := Rationals(); theta := -1;
  else F<theta> := CyclotomicField(m); end if;
  gseq := [];
  ptr := 0;
  for pair in ndx do
    k, b_k := Explode(pair);
    A := ChangeRing(baseGroup(m,1,b_k),F);
    I1 := IdentityMatrix(F,ptr);
    I_k := IdentityMatrix(F,k);
    ptr +:= k*b_k;
    I2 := IdentityMatrix(F,n-ptr);
    gens := [DiagonalJoin(<I1,TensorProduct(A.i,I_k),I2>) : i in [1..Ngens(A)]];
    Append(~gseq,gens);
  end for;
  return gseq;
end function;

standardComplement := function(m,p,n0,lambda)
  gseq := stdRefCompGens(m,p,n0,lambda);
  n := n0 + &+lambda;
  H := sub< ShephardTodd(m,p,n) | &cat gseq >;
  if n0 ne 0 or p eq 1 then return H; end if;
  ndxfrm := indexForm(lambda);
  e := GCD(p, GCD(lambda));
  e *:= &*[ p div GCD(p,k[1]) : k in ndxfrm ];
  e := e div p;
  if e eq 1 then return H; end if;

  if m eq 2 then
    F := Rationals();
    z := -1;
  else
    F<z> := CyclotomicField(m);
  end if;
  ptr := 0;
  gseq := [];
  for pair in ndxfrm do
    k, b_k := Explode(pair);
    if b_k eq 1 then
      ptr +:= 1;
    else
      G := ChangeRing(ShephardTodd(1,1,b_k),F);
      id1 := IdentityMatrix(F,ptr);
      id_k := IdentityMatrix(F,k);
      ptr +:= k*b_k;
      id2 := IdentityMatrix(F,n-ptr);
      Append(~gseq, [DiagonalJoin(<id1,TensorProduct(G.i,id_k),id2>) :
        i in [1..Ngens(G)]]);
    end if;
  end for;
  S := sub<GL(n,F) | &cat gseq>;
  dseq := diagPart(m,lambda);
  D := sub<GL(n,F) | &cat dseq > meet baseGroup(m,p,n);
  return sub< GL(n,F) | S, D >;
end function;

specialRoots := function(m,p,n0,lambda)
  n := n0 + &+lambda;
  if m le 2 then F := RationalField(); zeta := -1;
  else F<zeta> := CyclotomicField(m); end if;
  gamma := IsOdd(m) select zeta else zeta^2;
  h := IsOdd(m) select m else m div 2;
  assert IsOdd(h);
  V := VectorSpace(F,n);
  K := [ i eq 1 select 0 else Self(i-1) + lambda[i-1] : i in [1..#lambda+1] ];
  rts := &join[ {@ V.(i-1)-V.i : i in [K[j-1]+2..K[j]] @} : j in [2..#K]];
  if n0 eq 0 then delta0 := {@ @};
  else
    e := GCD(p, GCD(lambda));
    j := p div e;
    k := m div j;
    theta := zeta^k;
    d := K[#K]+1;
    delta0 := {@ V.(n-1) - theta^i*V.n : i in [0..j-1] @} join
              {@ zeta*V.(n-1) - theta^i*V.n : i in [0..j-1] @} join
              {@ V.(i-1)-V.i : i in [d+1..n-1] @};
    if p ne m then
      delta0 join:= {@ theta^i*V.n : i in [0..j-1] @}
             join {@ V.i : i in [d..n-1] @};
    end if;
  end if;
  return delta0 join &join[ {@ gamma^i*v : v in rts @} : i in [0..h-1]];
end function;

