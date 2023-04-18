loadPackage "Graphs"


graphEdges = {};
n = 9;

for i from 3 to n do (
    edgeList = {};
    for temp from 1 to i do (
        edgeList = append(edgeList, {temp, temp+i});
        edgeList = append(edgeList, {temp+i,temp});
    );

    for temp from  (i+2) to (2*i -1) do (
        edgeList = append(edgeList, {temp, temp+1});
        edgeList = append(edgeList, {temp+1,temp});
    );

    edgeList = append(edgeList, {2*i,i+1});
    edgeList = append(edgeList, {i+2, i+1});

    graphEdges = append(graphEdges, edgeList)
);



for j from 3 to n do (
    title = concatenate({"S", "_",toString(j), "_", "initialVersion" });
    ind = j - 3;
    title << graphEdges#ind << endl << close
)