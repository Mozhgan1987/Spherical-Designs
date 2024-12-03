/* computing the symmetry group of frames 

   Markus Grassl <markus.grassl@mpl.mpg.de>
   Shayne Waldron <swal089@math.auckland.ac.nz  >
   2017-03-01


   brief list of functions:
   - CanonicalGramian(Matrix)
   - MinimalCycleBasis(Graph)
   - FrameSymmetryMatrix(V)
     input: a (d x n) matrix V, the vectors are the columns of V
   - FrameSymmetry(L)
     input: a sequence of vectors in a d-dimensional vector space
   - FrameSymmetry(G)
     input: a canonical Gram matrix

   - permutation_to_matrix(V,perm)
     input: matrix V of the frame and a  permutation symmetry
     output: matrices M and D such that D*V eq V*perm*D

   - permutation_to_matrix_grp(V,sym)
     input: matrix V of the frame and its permutation symmetry

*/

declare verbose FrameSymmetry,2;


/* 

  for verbose level 2, output information on the computation of the cycle basis

/*
******************************************************************************
  Calculate the canonical Gramian P of the frame (v_j) given by the columns of 
  the d x n matrix V=[v1,...vn]. If V is an orthogonal projection this should
  return V.

  The base ring of V must be a field on which complex conjugation is defined.
******************************************************************************
*/

// If complex conjugation is defined on the base field, then we can take
// the HermitianTranspose
HermTranspose := function(B)
  T:=Transpose(B);
  T:=Parent(T)![ComplexConjugate(z):z in Eltseq(T)]; 
  return T;
end function;

// Define the standard inner product on vectors (linear in the first variable)
// This might need to be refined for other fields
ip := function(u,v)
  if Type(BaseRing(u)) in {FldRat,FldCyc,FldCom,FldRe} then 
    return InnerProduct(u,v);
  elif Type(BaseRing(u)) in {FldNum} then 
    return &+[Eltseq(u)[j]*ComplexConjugate(Eltseq(v)[j]): j in [1..#Eltseq(u)] ];
  else 
    error("The inner product is not defined over this field");
  end if;
end function;

// For F=ComplexField(m), NullspaceOfTranspose(V) fails.
// Better to do the calculations in matlab:
// [d n]=size(V), A=null(V); P=eye(n)-A*A'

myNullspaceOfTranspose:=function(V);
// a faster way to compute the nullpsace of the transpose of V
// WARNING: this is numerically unstable
  V1:=Transpose(EchelonForm(V));
  ind_pivot:=[];
  row:=1;
  for col:=1 to Ncols(V1) do
    while row le Nrows(V1) and Support(V1[row]) ne {col} do
      row+:=1;
    end while;
    if row le Nrows(V1) then
      Append(~ind_pivot,row);
    end if;
  end for;
  M0:=Matrix([V1[i]:i in [1..Nrows(V1)]|not i in ind_pivot]);
  M:=HorizontalJoin(M0,-One(MatrixRing(CoefficientRing(M0),Nrows(M0))));
  return [M[i]:i in [1..Nrows(M)]];
end function;

intrinsic CanonicalGramian(V::Mtrx)->Mtrx
{}
  F:=BaseRing(V); 
  n:=Ncols(V);
// Find the kernel of V (with usual matrix multiplication)
  
  vprintf FrameSymmetry: "  computing the kernel ";
  vtime FrameSymmetry: 
//  B:=myNullspaceOfTranspose(V);
  dep:=NullspaceOfTranspose(V);
  B:=Basis(dep);
// Apply Gram Schmidt without normalisation to the basis B 
  L:=[];
  vprintf FrameSymmetry: "  Gram-Schmidt orthogonalisation ";
  vtime FrameSymmetry: 
  for j in [1..#B] do
    v:=B[j]; 
    prj:=0*v;
    for k in [1..j-1] do
      prj+:=ip(v,L[k])/ip(L[k],L[k])*L[k];
    end for;
    Append(~L,v-prj);
  end for;
// To define the projection operator we need to use the Hermitian Transpose
  P:=Zero(MatrixRing(F,n));
  vprintf FrameSymmetry: "  computing the projection ";
  vtime FrameSymmetry: 
  for j in [1..#L] do
    v:=Transpose(Matrix([L[j]]));
    p0:=v*HermTranspose(v);
    P+:=1/Trace(p0)*p0;
  end for;
  I:=Identity(Parent(P));
  P:=I-P;
  return(P);
end intrinsic;

// Calculate the frame graph of a frame given by the columns of a 
// d x n matrix V=[v1,...vn]. 
intrinsic FrameGraph(V:Mtrx)->Grph
{Calculate the grame grpah a a frame given byt the columns of the matrix V}
  F:=BaseRing(V); 
  n:=Ncols(V);
  P:=CanonicalGramian(V);
  A:=Matrix([[P[j,k] eq 0 or j eq k select 0 else 1:k in [1..n]]:j in [1..n]]);
  return Graph<n|A>;
end intrinsic;


intrinsic MinimalCycleBasis(G::Grph:UseAut:=false)-> SeqEnum,SetIndx
{Computes a minimal cycle basis for the graph G. 
 The basis is returned as a sequence of binary vectors.
 The second return value is the indexed set of edges of G.
 When "UseAut" is set to true, the orbit of cycles under the autormorphism group fo the graph is used.
}

/* based on 
  Horton, J. D.,
  A polynomial-time algorithm to find the shortest cycle basis of a graph,
  SIAM Journal on Computing, vol. 16, no 2, April 1987, pp. 358-366
  
*/

  //optimization: perform the search for each component separately
  components:=ConnectedComponents(G);

  V:=Vertices(G);
  E:=Edges(G);
  if UseAut then
    vprintf FrameSymmetry,2: "computing the symmetry group of the graph ";
    vtime FrameSymmetry,2:
    aut,vertex_Gset,edge_Gset:=AutomorphismGroup(G);
  end if;
  V0:=KSpace(GF(2),#E);
  candidates:=[V0|];

  //for every vertex v and every edges e=(x,y), 
  //  we look for the shortest paths P(v,x) and P(v,y) from v to x and y, resp.
  //  then e+P(v,x)+P(v,y) forms a cycle
  //  note that some edges might occur twice, so that they cancel in the cycle
  //  Horton calls this "degenerate cases"

  // possibly use the orbit under the automorphism group of the graph
  ty:=Cputime();
  dim:=0;
  for C in components do
    G1:=sub<G|C>;
    V1:=Vertices(G1);
    E1:=Edges(G1);
    dim+:=#E1-#V1+1;
    for v in V1 do
      L_path:=ShortestPaths(v);
      for e in E1 do
        pts:=EndVertices(e);
        if not v in pts then
          path:=[Set(L_path[Position(V1,p)]):p in pts];
          //remove the common edges
          path:=path[1] sdiff path[2];
          if not e in path then
            Include(~path,e);
            if UseAut then
              vprintf FrameSymmetry,2: "computing the orbit of the cycle ";
              vtime FrameSymmetry,2:
              orbit:=Orbit(aut,edge_Gset,path);
            else
              orbit:={path};
            end if;
            for p in orbit do
    	      incidence:=V0!0;
    	      for x in p do
  	        incidence[Position(E,E!x)]+:=1;
  	      end for;
    	      Append(~candidates,incidence);
            end for;
          end if;
        end if;
      end for;
      V3:=sub<V0|{v:v in candidates|Weight(v) eq 3}>;
      vprintf FrameSymmetry,2: "  weights: %o, 3-cycle-space: %o, target: %o (%o s)\n",
         {* Weight(x):x in candidates *},Dimension(V3),dim,Cputime(ty);
      if Dimension(V3) eq dim then break v;end if;
    end for;
  end for;
  Sort(~candidates,func<a,b|Weight(a)-Weight(b)>);
  B:=SparseMatrix(GF(2),#E,#candidates);
  for i:=1 to #candidates do
    for j in Support(candidates[i]) do
      B[j,i]:=1;
    end for;
  end for;
  Echelonize(~B);
  basis:=[V0|candidates[Rep(Support(B[i]))]:i in [1..dim]];
  return basis,E;
end intrinsic;



EdgeCycleToSequence:=function(L);
// give a sequence or set of edges corresponding to a path, return an ordered set of vertices along the path
  L1:=[EndVertices(x):x in L];
  if #L1 eq 0 then
    return [];
  end if;
  if Set(Multiplicities({*x:x in a,a in L1*})) ne {2} then
    error("The sequence of edges is not a cycle");
  end if;
  // the initial vertex
  v1:=Rep(L1[1]);
  vertices:=[v1];
  v:=v1;
  repeat
    next_edge:=rep{x:x in L1|v in x};
    Exclude(~L1,next_edge);
    v:=Rep(Exclude(next_edge,v));
    Append(~vertices,v);
  until v eq v1;
  return vertices;
end function;

intrinsic FrameSymmetryMatrix(V::Mtrx:lowerbound:=0,eps:=1e-10)->GrpPerm
{}
  P:=CanonicalGramian(V);
  return FrameSymmetry(P:lowerbound:=lowerbound,eps:=eps);
end intrinsic;

intrinsic FrameSymmetry(L::[]:lowerbound:=0,eps:=1e-10)->GrpPerm
{}
  V:=Transpose(Matrix([v:v in L]));
  vprintf FrameSymmetry: "computing the canonical Gramian\n";
  vtime FrameSymmetry: 
  P:=CanonicalGramian(V);
  return FrameSymmetry(P:lowerbound:=lowerbound,eps:=eps);
end intrinsic;

intrinsic FrameSymmetry(G::Mtrx:
  lowerbound:=0,
  sort_blocks:=false,
  eps:=1e-10)->GrpPerm
{Compute the symmetry group of a frame given by a canonical Gram matrix as a permutation group.
 When the optional parameter "lowerbound" is set to a nonzero value, the algorithm terminates when the size symmetry group is not greater than the lowerbound.
 The parameter "sort_blocks" dettermines whether to sort the the blocsk by increasing size.
 The optional parameter "eps" defines the precision for floating point input.
}
// the input G is a Gram matrix
// CHECKING to be added

  //check whether we have exact or floating point arthmetics
  F:=CoefficientRing(G);
  exact:=not (Type(F) eq FldRe or Type(F) eq FldCom);
  if exact then 
    round:=func<x|x>;
  else
    M:=Round(1/eps);
    round:=func<x|Round(M*x)>;
// the following MIGHT give the anti-unitary symmetries
//    round:=func<x|Rep({Round(M*x),Round(M*ComplexConjugate(x))})>;
  end if;

  n:=Nrows(G);
  A:=Matrix([[i eq j or G[i,j] eq 0 select 0 else 1:j in [1..n]]:i in [1..n]]);
  frame_graph:=Graph<n|A>;

  //determine they symmetry group of the 1-cycles and 2-cycles
  G_abs:=Matrix([[round(G[i,j]*G[j,i]):j in [1..n]]:i in [1..n]]);
  vprintf FrameSymmetry: "computing the automorphism group of the 1- and 2-cycles ";
  vtime FrameSymmetry:
  sym0:=AutomorphismGroup(G_abs);
  sym:=sub<Sym(n)|[[i^g:i in [1..n]]:g in Generators(sym0)]>;
  if IsSymmetric(sym) then
    vprintf FrameSymmetry: "  initial group is the full symmetric group Sym(%o)\n",n;
  else
    vprintf FrameSymmetry: "  initial order: %o\n",#sym;
  end if;

  if #sym eq 1 then
    return sym;
  end if;

  current_order:=#sym;
  vertices:=Vertices(frame_graph);
  vprintf FrameSymmetry,2: "computing a minimal cycle basis:\n";
  vtime FrameSymmetry,2:
  cycle_basis,edges:=MinimalCycleBasis(frame_graph);
  dim:=#cycle_basis;

  EdgeCycleProduct:=function(L);
  // compute the m-product corresponding to the edge cycle L
    L_vertices:=EdgeCycleToSequence(L);
    indices:=[Position(vertices,v):v in L_vertices];
    prod:=1;
    for i:=2 to #indices do
      prod*:=G[indices[i-1],indices[i]];
    end for;
    return prod;
  end function;

  VertexCycleProduct:=function(L);
  // compute the m-product corresponding to the vertex cycle L
    indices:=[Position(vertices,v):v in L];
    prod:=1;
    for i:=2 to #indices do
      prod*:=G[indices[i-1],indices[i]];
    end for;
    return prod;
  end function;

  CycleProduct:=function(L);
  // compute the m-product corresponding to the cycle L given by indices
    //initialisation by the closing of the cycle
    if L[1] eq L[#L] then
      prod:=1;
    else
      prod:=G[L[#L],L[1]];
    end if;
    for i:=2 to #L do
      prod*:=G[L[i-1],L[i]];
    end for;
    return prod;
  end function;

  //initialise the space of the cycles processed so far
  C:=sub<Universe(cycle_basis)|>;

  while #cycle_basis ne 0 and #sym gt lowerbound do
    v_cycle:=cycle_basis[1];
    // convert the incidence vector of the cycle to a sequence of indices of vertices 
    cycle:=EdgeCycleToSequence({edges[i]:i in Support(v_cycle)});
    cycle:=[Position(vertices,x):x in cycle];

    m:=#cycle-1;
    vprintf FrameSymmetry: "selected the %o-cycle %o\n",m,cycle[1..m];
    vprintf FrameSymmetry: "  computing the orbit: ";
    vtime FrameSymmetry:
    if IsSymmetric(sym) then
      orbit:=GSet(sym,{x:x in Subsequences({1..n},m)|#Set(x) eq m});
    else
      orbit:=cycle[1..m]^sym;
    end if;
    vprintf FrameSymmetry:  "  orbit size: %o\n",#orbit;

    vprintf FrameSymmetry: "  computing the cycle-products: ";
    vtime FrameSymmetry:
    cycle_products:={<c,round(CycleProduct(c))>:c in orbit};

    values0:={* x[2]:x in cycle_products *};
    //sort the values by increasing frequencies
    if sort_blocks then
      values:=Setseq(Set(values0));
      Sort(~values,func<a,b|Multiplicity(values0,a)-Multiplicity(values0,b)>);
    else
       values:=Set(values0);
    end if;
    vprintf FrameSymmetry: "  %o different values (%o real)\n",#values,#{x:x in values|IsReal(x)};

    // now look at the blocks of the orbit with a fixed value of the cycle-product
    for val in values do
      part:={x[1]:x in cycle_products|x[2] eq val};

      // convert the cycles to vectors in the cycle space
      done:=[];
      for cyc0 in part do
        cyc:=Append(cyc0,cyc0[1]);
        v0:=C!0;
        for i:=2 to #cyc do
          edge:=edges!{vertices[cyc[i-1]],vertices[cyc[i]]};
          v0[Position(edges,edge)]+:=1;
        end for;
        Append(~done,v0);
      end for;
      // check which of the cycles are linear combination of the cycles processed so far
      vprintf FrameSymmetry: "  elements that have been processed: %o\n",{* v in C:v in done *};

      if #values gt 1 and exists{v:v in done|not v in C} then
        vprintf FrameSymmetry: "  computing the stabilizer for %o points: ",#part;
        vtime FrameSymmetry:
        sym:=Stabilizer(sym,orbit,part);
      end if;
      vprintf FrameSymmetry: "  current order: %o\n",#sym;
      C:=sub<Generic(C)|C,done>;
      vprintf FrameSymmetry: "  dimemsion of the cycle sub-space: %o (of %o)\n",Dimension(C),dim;
      if Dimension(C) eq dim then break;end if;
      // when the order has changed, we use the smaller group to compute the orbits
      if #sym ne current_order then
        current_order:=#sym;
        break;
      end if;
    end for;
    cycle_basis:=[x:x in cycle_basis|not x in C];
  end while;

  return sym;
end intrinsic;

intrinsic permutation_to_matrix(V::Mtrx,perm::GrpPermElt)->Mtrx,Mtrx
{}
// compute a matrix M such that M*V = V^perm*D with a diagonal matrix D
  // the very lazy approach
  d:=Nrows(V);
  n:=Ncols(V);
  V_transp:=Transpose(V);
  V_perm:=Transpose(Matrix([V_transp[i]:i in Eltseq(perm)]));
  P<[x]>:=PolynomialRing(CoefficientRing(V),d^2+n-1,"grevlex");
  M:=MatrixRing(P,d)!x[1..d^2];
  // fix the first phase to be 1
  D:=DiagonalMatrix([1] cat x[d^2+1..d^2+n-1]);
  bed:=Reduce(Eltseq(M*ChangeRing(V,P)-ChangeRing(V_perm,P)*D));
  id:=ideal<P|bed>;
  dim,vars:=Dimension(id);
  if dim gt 0 then
    printf "WARNING: %o free parameters\n",dim;
    id:=ideal<P|id,[id.i-1:i in vars]>;
  end if;
  M1:=MatrixRing(P,d)![NormalForm(x,id):x in Eltseq(M)];
  D1:=DiagonalMatrix([NormalForm(x,id):x in Eltseq(D)]);
  if #bed eq Rank(id) then
    M1:=ChangeRing(M1,CoefficientRing(V));
    D1:=ChangeRing(D1,CoefficientRing(V));
  end if;
  return M1,D1,bed;
end intrinsic;


intrinsic permutation_to_matrix_grp(V::Mtrx,sym::GrpPerm)->Grp
{}
// compute a matrix M such that M*V = V^perm*D with a diagonal matrix D
  // the very lazy approach
  F:=CoefficientRing(V);
  d:=Nrows(V);
  n:=Ncols(V);
  V_transp:=Transpose(V);
  P<[x]>:=PolynomialRing(F,d^2+n-1,"grevlex");
  M:=MatrixRing(P,d)!x[1..d^2];
  // fix the first phase to be 1
  D:=DiagonalMatrix([1] cat x[d^2+1..d^2+n-1]);
  grp:=sub<GL(d,F)|>;
  for perm in Generators(sym) do
    V_perm:=Transpose(Matrix([V_transp[i]:i in Eltseq(perm)]));
    bed:=Reduce(Eltseq(M*ChangeRing(V,P)-ChangeRing(V_perm,P)*D));
    id:=ideal<P|bed>;
    dim,vars:=Dimension(id);
    if dim gt 0 then
      printf "WARNING: %o free parameters\n",dim;
      id:=ideal<P|id,[id.i-1:i in vars]>;
    end if;
    M1:=MatrixRing(F,d)![NormalForm(x,id):x in Eltseq(M)];
    D1:=DiagonalMatrix(F,[NormalForm(x,id):x in Eltseq(D)]);
    if not HasFiniteOrder(M1) then
      "WARNING: infinite order\n";
    end if;
    grp:=sub<Generic(grp)|grp,M1>;
  end for;
  return grp;
end intrinsic;
