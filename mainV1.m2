loadPackage "Graphs"
loadPackage "PhylogeneticTrees"
loadPackage "PHPack"
loadPackage "Elimination"
loadPackage "NumericalAlgebraicGeometry"
loadPackage "PrimaryDecomposition"


--Here is where we initialize our graph
--G = digraph ({{1,2},{2,1},{2,3},{1,3},{3,4},{4,3},{5,1},{1,5},{6,2},{2,6}}, EntryMode => "edges")
--G = digraph ( {{1, 5}, {5, 1}, {2, 6}, {6, 2}, {3, 7}, {7, 3}, {4, 8}, {8, 4}, {5, 6}, {6, 5}, {6, 7}, {7, 6}, {5, 8}, {7, 8}}, EntryMode => "edges")
--G = digraph ({{1, 4}, {4, 1}, {2, 5}, {5, 2}, {3, 6}, {6, 3}, {4, 5}, {5, 4}, {4, 6}, {5, 6}}, EntryMode => "edges")
G = digraph ( {{1, 6}, {6, 1}, {2, 7}, {7, 2}, {3, 8}, {8, 3}, {4, 9}, {9, 4}, {5, 10}, {10, 5}, {7, 8}, {8, 7}, {8, 9}, {9, 8}, {9, 10}, {10, 9}, {10, 6}, {7, 6}}, EntryMode => "edges")


--list of reticulation vertices
ret = {};
--gets a list of edges
e = edges G;
--gets a list of vertices
v = vertices G;

--here we identify and make our list of reticulation vertices
for i from 1 to #v do if degreeIn(G,i) > degreeOut(G,i) then ret = append(ret,i)

--here we are going to get our list of directed edges to our reticulation vertices
edgeList = {}
for i in ret do(
    forRetVertex = {};
    for j from 1 to #v do(
        if  (not member({i,j},e)) and (member({j,i},e)) then (forRetVertex = append(forRetVertex,{j,i})));
    edgeList = append(edgeList,forRetVertex) 
)

--here we are just going to generate our list of leaves
leafList = {}
for i from 1 to #v do (
    if (degreeIn(G,i) == 1) and (degreeOut(G,i) == 1) then (
        leafList = append(leafList,i)
    )
)


--here is a recursive binary generator,it returns all the binary strings of a certain length
genBi = j -> (
    bi = {};
    g = (n,ap) -> (
        if ((length ap) == n) 
            then( 
                bi = append(bi,ap)
            )
        else (
            g(n,append(ap,0)); 
            g(n,append(ap,1)); 
        )
    );
    g(j,{});
    return bi;
)

--here we want to generate our list of trees upon which we are going to run our alg, we generate these by systemically removing the edges going into reticulation vertices
treeOptions = genBi(length edgeList#0);
treeList = {};

for i in treeOptions do(
    tempTree = G;
    sm = 0;
    for j in i do (
        sm = mod(sm + j, 2);
    );
    print(sm);
    if sm == 1 then (
        for k from 0 to length(i)-1 do(
            if i#k == 0 then (
                edgetoDelete = edgeList#0#k;
                tempTree = deleteEdges(tempTree, {edgetoDelete});
            );
         );
         treeList = append(treeList, tempTree);
    ); 
)


--now we need to define the rings we are working in
qUnderscores = {}
biCombs = genBi(length leafList)
for i in biCombs do (
    isZ = 0;
    for j in i do (
        isZ = isZ + j
    );
    if mod(isZ,2) == 0 then(
        qUnderscores = append(qUnderscores, i)
    )
)

qs = []
for j in qUnderscores do (
    qs = append(qs, q_j)
)

--this defines one polynomial ring
R = QQ qs

--Okay!! Things to do: define S,  cut every edge of the graph for every q_, and then count # of leaves for each tree, this will give us a polynomial for each q!

as = []
for i from 1 to 2*(length leafList) do(
    stg0 = concatenate({"a", toString(i) ,"_0"});
    as = append(as,stg0);
    stg1 = concatenate({"a", toString(i) ,"_1"});
    as = append(as,stg1);
)

S = QQ as;

cnt = 0
parameterization = {};
for i in qs do (
    --every input has a specific output, we will count these here
    entry = 0;
    for j in treeList do (
        Edi = edges j;
        unDi = graph(Edi);
        E = edges unDi;
        edgeExponents = {};
        edgeSubscripts = {};
        for k from 0 to #E -1 do (
            lis =  toList(E#k);
            eRem = deleteEdges(unDi,{lis});
            comps = connectedComponents eRem;
            sm = 0;
            for m from 0 to (length (comps#0)) -1 do(
                if (
                    member(comps#0#m,leafList) 
                )
                then (
                    indx = (comps#0#m) - 1;
                    val = qUnderscores#cnt#indx;
                    sm = mod(sm + val, 2)
                )
            );
            edgeSubscripts = append(edgeSubscripts,sm);
            edgeExponents = append(edgeExponents,k)
        );
        prod;
        for k from 0 to #edgeSubscripts-1 do(
            if k == 0 then (
                sym = concatenate("a",toString(k+1),"_",toString(edgeSubscripts#(k)));
                prod = S_sym;
            ) else (
                sym = concatenate("a",toString(k+1),"_",toString(edgeSubscripts#(k)));
                tem = prod * S_sym ;
                prod = tem
            )
        );
        entry = entry + prod;
    );
    cnt = cnt + 1;
    parameterization = append(parameterization, entry);
)


phi = map(S,R,parameterization)
I = ker phi


--Now for homotopy continuation! 
--spent a lot of time messing with homotopy continuation..... I will return to it if necessary


------- Trying something different...

probabilisticEDDegree = method();

probabilisticEDDegree Ideal := ZZ => I -> (
  --ring from your ideal
  R = ring I;
  --transpose jacobian
  jacI := transpose jacobian I;
  --codim of ideal, defined by the dim of our full ring - dim of our variety
  c = codim I;
  --this is creating the base equation, our ideal
  Ising := I + minors(c, jacI);
  u = gens R / (i -> random(coefficientRing R));
  local Ibar;
  Ibar = I + minors(c+1, matrix{u} - vars R || jacI);
  J = saturate(Ibar, Ising);
  return J
)


sys = probabilisticEDDegree(I)
system = {}
for i from 0 to (#sys -1) do(
    system = append(system,sys_i)
)

sols = solveSystem( (polySystem system))
