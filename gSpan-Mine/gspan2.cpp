#include <bits/stdc++.h>
#include "graph.h"
#define XX first
#define YY second
using namespace std;

vector <Graph> database;

void constructGraphs(){
	FILE* fp=fopen(INPUTFILE, "r");
	char str[5];
	int u, v, label, label_u, label_v;
	double p;
	int cnt=-1;
	int sz;
	bool isFirst;
	int maxNode;
	while(fscanf(fp, "%s", str)!=EOF){
		if(str[0]=='t'){
			fscanf(fp, "%s %d", str, &v);
			if(v==-1) break;
			database.push_back(Graph());
			cnt++;
			isFirst=true;
			maxNode=0;
		}
		else if(str[0]=='v'){
			fscanf(fp, "%d %d", &v, &label);
			label=relabelledNodeLabels[label];
			maxNode=max(maxNode, v);
			if(label==-1) continue;
			database[cnt].nodesWithLabel[label].push_back(v);
			if(v==(int)database[cnt].nodeLabel.size()){
				database[cnt].nodeLabel.push_back(label);
			}
			else if(v>(int)database[cnt].nodeLabel.size()){
				database[cnt].nodeLabel.resize(v+1, -1);
				database[cnt].nodeLabel[v]=label;
			}
			else{
				database[cnt].nodeLabel[v]=label;
			}
		}
		else if(str[0]=='e'){
			if(isFirst){
				database[cnt].adj.resize(maxNode+1, vector <int>());
				if((int)database[cnt].nodeLabel.size()<=maxNode){
					database[cnt].nodeLabel.resize(maxNode+1, -1);
				}
				isFirst=false;
			}
			fscanf(fp, "%d %d %d %lf", &u, &v, &label, &p);
			//printf("e %d %d %d %f scanned\n", u, v, label, p);
			label=relabelledEdgeLabels[label];
			label_u=database[cnt].nodeLabel[u];
			label_v=database[cnt].nodeLabel[v];
			if(label==-1) continue;
			if(label_u==-1) continue;
			if(label_v==-1) continue;
			if(frequentTuples.find({{nodeLabelOrder[label_u], edgeLabelOrder[label]}, nodeLabelOrder[label_v]})==frequentTuples.end()) continue;
			database[cnt].edges.push_back(Edge(u, v, label, p));
			sz=(int)database[cnt].edges.size();
			database[cnt].adj[u].push_back(sz-1);
			database[cnt].adj[v].push_back(sz-1);
		}
	}
	fclose(fp);
}



vector <DFSTuple> getRightMostPathExtensions(DFSCode code, vector <Embedding> embeddings){
	map <DFSTuple, int> extensionFrequency;
	map <DFSTuple, int> extensionLast;
	vector <DFSTuple> result;
	int rmChild, u, gid, v, elabel, ind;
	bool flag;
	vector <int> path;
	DFSTuple extension;
	for(auto embedding: embeddings){
		rmChild=code.getRightMostChild();
		path=code.getRightMostPath();
		gid=embedding.gid;
		u=embedding.getMappedNode(rmChild);
		if(u==-1) continue;

		/*generate backward edges*/
		for(auto edgeID: database[gid].adj[u]){
			v=database[gid].edges[edgeID].getOtherNode(u);
			elabel=database[gid].edges[edgeID].label;
			flag=false;
			for(int i=0; i<(int)path.size()-2; i++){
				if(embedding.getMappedNode(path[i])==v){
					flag=true;
					ind=path[i];
					break;
				}
			}
			if(!flag){
				continue;
			}
			for(auto edge: embedding.edges){
				if(edge==edgeID){
					flag=false;
					break;
				}
			}
			if(!flag){
				continue;
			}
			extension=DFSTuple(rmChild, ind, database[gid].nodeLabel[u], elabel, database[gid].nodeLabel[v]);
			if(extensionLast[extension]<(gid+1)){
				extensionLast[extension]=gid+1;
				extensionFrequency[extension]++;
				if(extensionFrequency[extension]==min_sup){
					result.push_back(extension);
				}
			}
		}
		/*Generate forward extensions*/
		for(auto rmNode: path){
			u=embedding.getMappedNode(rmNode);
			if(u==-1) continue;
			for(auto edgeID: database[gid].adj[u]){
				v=database[gid].edges[edgeID].getOtherNode(u);
				elabel=database[gid].edges[edgeID].label;
				flag=true;
				for(auto node: embedding.nodesMapped){
					if(node==v){
						flag=false;
						break;
					}
				}
				if(!flag){
					continue;
				}
				extension=DFSTuple(rmNode, rmChild+1, database[gid].nodeLabel[u], elabel, database[gid].nodeLabel[v]);
				if(extensionLast[extension]<(gid+1)){
					extensionLast[extension]=gid+1;
					extensionFrequency[extension]++;
					if(extensionFrequency[extension]==min_sup){
						result.push_back(extension);
					}
				}
			}
		}
	}
	sort(result.begin(), result.end());
	return result;
}

DFSTuple getMinimumExtension(DFSCode code, vector <Embedding> embeddings, Graph graph){
	DFSTuple minExtension;
	int rmChild, u, v, elabel, ind;
	bool flag;
	vector <int> path;
	DFSTuple extension;
	bool isFirst=true;
	for(auto embedding: embeddings){
		rmChild=code.getRightMostChild();
		path=code.getRightMostPath();
		u=embedding.getMappedNode(rmChild);
		if(u==-1) continue;
		for(auto edgeID: graph.adj[u]){
			v=graph.edges[edgeID].getOtherNode(u);
			elabel=graph.edges[edgeID].label;
			flag=false;
			for(int i=0; i<(int)path.size()-2; i++){
				if(embedding.getMappedNode(path[i])==v){
					flag=true;
					ind=path[i];
					break;
				}
			}
			if(!flag){
				continue;
			}
			for(auto tuple: code.tuples){
				if(tuple.u>tuple.v){
					if(tuple.u==rmChild){
						if(tuple.v==ind){
							flag=false;
						}
					}
				}
			}
			if(!flag){
				continue;
			}
			extension=DFSTuple(rmChild, ind, graph.nodeLabel[u], elabel, graph.nodeLabel[v]);
			if(isFirst){
				minExtension=extension;
				isFirst=false;
			}
			else if(extension<minExtension){
				minExtension=extension;
			}
		}
		/*Generate forward extensions*/
		for(auto rmNode: path){
			u=embedding.getMappedNode(rmNode);
			if(u==-1) continue;
			for(auto edgeID: graph.adj[u]){
				v=graph.edges[edgeID].getOtherNode(u);
				elabel=graph.edges[edgeID].label;
				flag=true;
				for(auto node: embedding.nodesMapped){
					if(node==v){
						flag=false;
						break;
					}
				}
				if(!flag){
					continue;
				}
				extension=DFSTuple(rmNode, rmChild+1, graph.nodeLabel[u], elabel, graph.nodeLabel[v]);
				if(isFirst){
					minExtension=extension;
					isFirst=false;
				}
				else if(extension<minExtension){
					minExtension=extension;
				}
			}
		}
	}
	return minExtension;
}

bool isMin(DFSCode code){
	Graph graph=Graph(code);
	DFSTuple extension=graph.getMinTuple();
	DFSCode tempCode;
	vector <Embedding> embeddings;
	int sz=code.tuples.size();
	int cnt=0;
	for(auto tuple: code.tuples){
		if(extension<tuple){
			return false;
		}
		if(cnt>(sz-2)){
			return true;
		}
		cnt++;
		tempCode.tuples.push_back(extension);
		embeddings=graph.extendEmbeddings(0, embeddings, extension);
		extension=getMinimumExtension(tempCode, embeddings, graph);
	}
	return true;
}
int fsub=0;
void printSubgraphPattern(DFSCode code){
	printf("Subgraph pattern %d\n", fsub);
	for(auto tuple: code.tuples){
		printf("%d %d %d %d %d\n", tuple.u, tuple.v, nodeLabelOrder[tuple.label_u], edgeLabelOrder[tuple.eLabel], nodeLabelOrder[tuple.label_v]);
	}
}
bool cmpEmbeddings(Embedding a, Embedding b){
    for(int i=0; i<(int)a.edges.size(); i++){
        if(a.edges[i]<b.edges[i]) return true;
        if(a.edges[i]>b.edges[i]) return false;
    }
    return false;
}

struct EdgeEmbeddingGraph{
    int no_of_edges;
    int no_of_embeddings;
    vector < vector <int> >  edge_to_embedding;
    vector < vector <int> > embedding_to_edge;
    vector <double> edgeP;
    vector <double> inherentP;
    EdgeEmbeddingGraph(){
        no_of_edges=0;
        no_of_embeddings=0;
        edge_to_embedding.push_back(vector <int>());
        embedding_to_edge.push_back(vector <int>());
        edgeP.push_back(0);
        inherentP.push_back(0);
    }


    bool isEqual(Embedding a, Embedding b){
        for(int i=0; i<(int)a.edges.size(); i++){
            if(a.edges[i]!=b.edges[i]) return false;
        }
        return true;
    }

    EdgeEmbeddingGraph(vector <Embedding> embeddings){  /*Assumes all embeddings belong to the same graph*/
        no_of_edges=0;
        no_of_embeddings=0;
        map <int, int> edgeNo;
        edge_to_embedding.push_back(vector <int>());
        embedding_to_edge.push_back(vector <int>());
        edgeP.push_back(0);
        inherentP.push_back(0);
        for(int i=0; i<(int)embeddings.size(); i++){
            sort(embeddings[i].edges.begin(), embeddings[i].edges.end());
        }
        sort(embeddings.begin(), embeddings.end(), cmpEmbeddings);
        for(auto embedding: embeddings){
            for(auto edge: embedding.edges){
                if(edgeNo.find(edge)==edgeNo.end()){
                    no_of_edges++;
                    edge_to_embedding.push_back(vector <int>());
                    edgeP.push_back(1-database[embedding.gid].edges[edge].p);
                    edgeNo[edge]=no_of_edges;
                }
            }
        }
        for(int i=0; i<(int)embeddings.size(); i++){
            if(i==0 || !isEqual(embeddings[i], embeddings[i-1])){
                no_of_embeddings++;
                embedding_to_edge.push_back(vector <int> ());
                inherentP.push_back(0);
                for(auto edge: embeddings[i].edges){
                    edge_to_embedding[edgeNo[edge]].push_back(no_of_embeddings);
                    embedding_to_edge[no_of_embeddings].push_back(edgeNo[edge]);
                }
            }
        }
    }

    void print(){
        printf("No of Edges=%d\n", no_of_edges);
        printf("No of embeddings=%d\n", no_of_embeddings);
        for(int i=1; i<=no_of_edges; i++){
            printf("Edge %d connected to embeddings: ", i);
            for(auto embedding: edge_to_embedding[i]){
                printf("%d ", embedding);
            }
            printf("\n");
            printf("Probability of edge not existing: %f\n", edgeP[i]);
        }
        for(int i=1; i<=no_of_embeddings; i++){
            printf("Embedding %d connected to edges: ", i);
            for(auto edge: embedding_to_edge[i]){
                printf("%d ", edge);
            }
            printf("\n");
            printf("Probability of embedding not existing: %f\n", inherentP[i]);
        }
    }
};

EdgeEmbeddingGraph compress(EdgeEmbeddingGraph g){
    EdgeEmbeddingGraph result;
    result.no_of_embeddings=g.no_of_embeddings;
    vector <int> remapping;
    remapping.resize(g.no_of_edges+1, -1);
    result.no_of_embeddings=g.no_of_embeddings;
    result.inherentP.resize(result.no_of_embeddings+1, 0);
    int cnt=0;
    for(auto adj: g.edge_to_embedding){
        if(adj.size()>1){
            result.no_of_edges++;
            remapping[cnt]=result.no_of_edges;
            //printf("Remapping %d to %d\n", cnt, remapping[cnt]);;
            result.edge_to_embedding.push_back(adj);
            //printf("Result's edge to embedding size is now %d\n", (int)result.edge_to_embedding.size());
            result.edgeP.push_back(g.edgeP[cnt]);
        }
        else if(adj.size()==1){
            for(auto em: adj){
                result.inherentP[em]+=g.edgeP[cnt];
            }
        }
        cnt++;
    }
    int v;
    for(int i=1; i<=g.no_of_embeddings; i++){
        result.embedding_to_edge.push_back(vector <int>());
        for(int j=0; j<(int)g.embedding_to_edge[i].size(); j++){
            v=remapping[g.embedding_to_edge[i][j]];
            if(v!=-1){
                result.embedding_to_edge[i].push_back(v);
            }
        }
    }
    return result;
}


vector <EdgeEmbeddingGraph> split(EdgeEmbeddingGraph g){
    vector <EdgeEmbeddingGraph> result;
    vector < pair <int, int> > edgeComponent;
    vector < pair <int, int> > embeddingComponent;
    int componentCount=0;
    int edgesInComponent;
    int embeddingsInComponent;
    edgeComponent.resize(g.no_of_edges+1, {-1, -1});
    embeddingComponent.resize(g.no_of_embeddings+1, {-1, -1});
    stack < pair <int, int> > dfsS;
    for(int i=1; i<=g.no_of_edges; i++){
        if(edgeComponent[i].XX==-1){
            dfsS.push({0, i});
            edgeComponent[i]={componentCount, 1};
            edgesInComponent=1;
            embeddingsInComponent=0;
            int u;
            while(!dfsS.empty()){
                if(dfsS.top().XX==0){
                    u=dfsS.top().YY;
                    dfsS.pop();
                    for(auto v: g.edge_to_embedding[u]){
                        if(embeddingComponent[v].XX!=-1) continue;
                        dfsS.push({1, v});
                        embeddingsInComponent++;
                        embeddingComponent[v]={componentCount, embeddingsInComponent};
                    }
                }
                else{
                    u=dfsS.top().YY;
                    dfsS.pop();
                    for(auto v: g.embedding_to_edge[u]){
                        if(edgeComponent[v].XX!=-1) continue;
                        dfsS.push({0, v});
                        edgesInComponent++;
                        edgeComponent[v]={componentCount, edgesInComponent};
                    }
                }
            }
            componentCount++;
        }
    }
    for(int i=1; i<=g.no_of_embeddings; i++){
        if(embeddingComponent[i].XX==-1){
            dfsS.push({1, i});
            embeddingComponent[i]={componentCount, 1};
            edgesInComponent=0;
            embeddingsInComponent=1;
            int u;
            while(!dfsS.empty()){
                if(dfsS.top().XX==0){
                    u=dfsS.top().YY;
                    dfsS.pop();
                    for(auto v: g.edge_to_embedding[u]){
                        dfsS.push({1, v});
                        embeddingsInComponent++;
                        embeddingComponent[v]={componentCount, embeddingsInComponent};
                    }
                }
                else{
                    u=dfsS.top().YY;
                    dfsS.pop();
                    for(auto v: g.embedding_to_edge[u]){
                        dfsS.push({0, v});
                        edgesInComponent++;
                        edgeComponent[v]={componentCount, edgesInComponent};
                    }
                }
            }
            componentCount++;
        }
    }
    for(int i=0; i<componentCount; i++){
        result.push_back(EdgeEmbeddingGraph());
    }
    for(int i=1; i<=g.no_of_edges; i++){
        result[edgeComponent[i].XX].no_of_edges++;
        result[edgeComponent[i].XX].edge_to_embedding.push_back(vector <int>());
        result[edgeComponent[i].XX].edgeP.push_back(0);
    }
    for(int i=1; i<=g.no_of_embeddings; i++){
        result[embeddingComponent[i].XX].no_of_embeddings++;
        result[embeddingComponent[i].XX].embedding_to_edge.push_back(vector <int>());
        result[embeddingComponent[i].XX].inherentP.push_back(0);
    }
    for(int i=1; i<=g.no_of_edges; i++){
        result[edgeComponent[i].XX].edgeP[edgeComponent[i].YY]=g.edgeP[i];
        for(auto v: g.edge_to_embedding[i]){
            result[edgeComponent[i].XX].edge_to_embedding[edgeComponent[i].YY].push_back(embeddingComponent[v].YY);
        }
    }
    for(int i=1; i<=g.no_of_embeddings; i++){
        result[embeddingComponent[i].XX].inherentP[embeddingComponent[i].YY]=g.inherentP[i];
        for(auto v: g.embedding_to_edge[i]){
            result[embeddingComponent[i].XX].embedding_to_edge[embeddingComponent[i].YY].push_back(edgeComponent[v].YY);
        }
    }
    return result;
}

EdgeEmbeddingGraph keepEdge(EdgeEmbeddingGraph g, int ind){
    EdgeEmbeddingGraph result;
    result.no_of_edges=g.no_of_edges-1;
    result.no_of_embeddings=g.no_of_embeddings;
    for(int i=1; i<=g.no_of_edges; i++){
        if(i==ind) continue;
        result.edge_to_embedding.push_back(g.edge_to_embedding[i]);
        result.edgeP.push_back(g.edgeP[i]);
    }
    for(int i=1; i<=g.no_of_embeddings; i++){
        result.embedding_to_edge.push_back(vector <int> ());
        result.inherentP.push_back(g.inherentP[i]);
        for(auto v: g.embedding_to_edge[i]){
            if(v<ind){
                result.embedding_to_edge[i].push_back(v);
            }
            else if(v>ind){
                result.embedding_to_edge[i].push_back(v-1);
            }
        }
    }
    return result;
}

EdgeEmbeddingGraph dontKeepEdge(EdgeEmbeddingGraph g, int ind){
    EdgeEmbeddingGraph result;
    result.no_of_edges=g.no_of_edges-1;
    result.no_of_embeddings=g.no_of_embeddings-g.edge_to_embedding[ind].size();
    vector <int> remappedEdges;
    vector <int> remappedEmbeddings;
    remappedEdges.resize(g.no_of_edges+1, -1);
    remappedEmbeddings.resize(g.no_of_embeddings+1, -1);
    remappedEdges[ind]=0;
    for(auto v: g.edge_to_embedding[ind]){
        remappedEmbeddings[v]=0;
    }
    int cnt=0;
    for(int i=1; i<=g.no_of_edges; i++){
        if(remappedEdges[i]==-1){
            cnt++;
            remappedEdges[i]=cnt;
        }
        else remappedEdges[i]=-1;
    }
    cnt=0;
    for(int i=1; i<=g.no_of_embeddings; i++){
        if(remappedEmbeddings[i]==-1){
            cnt++;
            remappedEmbeddings[i]=cnt;
        }
        else remappedEmbeddings[i]=-1;
    }
    for(int i=1; i<=g.no_of_edges; i++){
        if(remappedEdges[i]==-1) continue;
        result.edge_to_embedding.push_back(vector <int> ());
        for(auto v: g.edge_to_embedding[i]){
            if(remappedEmbeddings[v]==-1) continue;
            result.edge_to_embedding[remappedEdges[i]].push_back(remappedEmbeddings[v]);
        }
        result.edgeP.push_back(g.edgeP[i]);
    }
    for(int i=1; i<=g.no_of_embeddings; i++){
        if(remappedEmbeddings[i]==-1) continue;
        result.embedding_to_edge.push_back(vector <int> ());
        for(auto v: g.embedding_to_edge[i]){
            if(remappedEdges[v]==-1) continue;
            result.embedding_to_edge[remappedEmbeddings[i]].push_back(remappedEdges[v]);
        }
        result.inherentP.push_back(g.inherentP[i]);
    }
    return result;
}

map <int, int> keepSize(EdgeEmbeddingGraph e, int ind){
    printf("In keep\n");
    map <int, int> result;
    vector <bool> visitedEd, visitedEm;
    visitedEd.resize(e.no_of_edges+1, false);
    visitedEm.resize(e.no_of_embeddings+1, false);
    visitedEd[ind]=true;
    stack < pair < int, int> > stk;
    int componentSize;
    pair <int, int> temp;
    for(int i=1; i<=e.no_of_edges; i++){
        if(!visitedEd[i]){
            visitedEd[i]=true;
            componentSize=1;
            stk.push({0, i});
            while(!stk.empty()){
                temp=stk.top();
                printf("Stack top: %d %d\n", temp.XX, temp.YY);
                stk.pop();
                if(temp.XX==0){
                    for(auto v: e.edge_to_embedding[temp.YY]){
                        if(visitedEm[v]==false){
                            visitedEm[v]=true;
                            stk.push({1, v});
                        }
                    }
                }
                else{
                    for(auto v: e.embedding_to_edge[temp.YY]){
                        if(visitedEd[v]==false){
                            visitedEd[v]=true;
                            stk.push({0, v});
                            componentSize++;
                        }
                    }
                }
            }
            result[componentSize]++;
        }
    }
    return result;
}

map <int, int> dontkeepSize(EdgeEmbeddingGraph e, int ind){
    printf("In dont keep\n");
    map <int, int> result;
    vector <bool> visitedEd, visitedEm;
    visitedEd.resize(e.no_of_edges+1, false);
    visitedEm.resize(e.no_of_embeddings+1, false);
    visitedEd[ind]=true;
    for(auto v: e.edge_to_embedding[ind]){
        visitedEm[ind]=true;
    }
    stack < pair < int, int> > stk;
    int componentSize;
    pair <int, int> temp;
    for(int i=1; i<=e.no_of_edges; i++){
        if(!visitedEd[i]){
            visitedEd[i]=true;
            componentSize=1;
            stk.push({0, i});
            while(!stk.empty()){
                temp=stk.top();
                stk.pop();
                printf("Stack top: %d %d\n", temp.XX, temp.YY);
                if(temp.XX==0){
                    for(auto v: e.edge_to_embedding[temp.YY]){
                        if(visitedEm[v]==false){
                            visitedEm[v]=true;
                            stk.push({1, v});
                        }
                    }
                }
                else{
                    for(auto v: e.embedding_to_edge[temp.YY]){
                        if(visitedEd[v]==false){
                            visitedEd[v]=true;
                            stk.push({0, v});
                            componentSize++;
                        }
                    }
                }
            }
            result[componentSize]++;
        }
    }
    return result;
}

map <int, int> generateCombinedMap(map <int, int> mp1, map <int, int> mp2){
    printf("In gen\n");
    map<int, int> result;
    map<int, int>::iterator itr;
    for(itr=mp1.begin(); itr!=mp1.end(); itr++){
        result[itr->first]+=(itr->second);
    }
    for(itr=mp2.begin(); itr!=mp2.end(); itr++){
        result[itr->first]+=(itr->second);
    }
    return result;
}

map <int, int> getEstimate(EdgeEmbeddingGraph e, int ind){
    printf("In function\n");
    map <int, int> mp=generateCombinedMap(keepSize(e, ind), dontkeepSize(e, ind));
    printf("Combined map generated\n");
    map <int, int>::iterator it;
    int carry=0;
    int last=0;
    int need;
    int cnt=0;
    for(it=mp.begin(); it!=mp.end(); it++){
        if(last!=0){
            need=1;
            cnt=0;
            while(cnt<((it->first)-last)){
                need<<=1;
                cnt++;
                if(need>carry) break;
            }
            if(need<=carry){
                mp[it->first]+=(carry/need);
                carry%=need;
                mp[last]=carry;
            }
        }
        carry=mp[it->first];
        last=it->first;
    }
    need=1;
    int offset=0;
    while((need<<1)<=carry){
        need<<=1;
        offset++;
    }
    if(offset){
        mp[last+offset]=1;
        mp[last]=(carry-need);
    }
    return mp;
}

void gSpan(DFSCode code, vector <Embedding> embeddings){
	printSubgraphPattern(code);
	fsub++;
    vector < vector <Embedding> > slices;
    vector < EdgeEmbeddingGraph > factorGraphs;
    for(int i=0; i<(int)embeddings.size(); i++){
        if(i==0 || embeddings[i].gid!=embeddings[i-1].gid){
            slices.push_back(vector <Embedding> ());
        }
        slices[(int)slices.size()-1].push_back(embeddings[i]);
    }
    for(auto slice: slices){
        factorGraphs.push_back(EdgeEmbeddingGraph(slice));
    }
    for(auto graph: factorGraphs){
        printf("Before compressing\n");
        graph.print();
        graph=compress(graph);
        printf("After compressing\n");
        graph.print();
        vector <EdgeEmbeddingGraph> graphs=split(graph);
        printf("After splitting\n");
        for(auto g: graphs){
            g.print();
            if(g.no_of_edges>=1){
                printf("Predicted complexity if %d is removed:\n", (1+g.no_of_edges)>>1);
                map <int, int> complexity=getEstimate(g, (1+g.no_of_edges)>>1);
                printf("Function returned\n");
                map <int, int>::iterator it;
                for(it=complexity.begin(); it!=complexity.end(); it++){
                    printf("%d: %d\n", it->first, it->second);
                }
                EdgeEmbeddingGraph temp1=keepEdge(g, (1+g.no_of_edges)>>1), temp2=dontKeepEdge(g, (1+g.no_of_edges)>>1);
                printf("If edge %d is kept\n", (1+g.no_of_edges)>>1);
                temp1.print();
                printf("If edge %d is not kept\n", (1+g.no_of_edges)>>1);
                temp2.print();
            }
        }
        fflush(stdout);
    }
	vector <DFSTuple> extensions=getRightMostPathExtensions(code, embeddings);


	DFSCode newCode;
	for(auto extension: extensions){
		newCode=code;
		newCode.tuples.push_back(extension);
		if(!isMin(newCode)) continue;
		vector <Embedding> newEmbeddings, tempEmbeddings;
		for(auto embedding: embeddings){
			tempEmbeddings=database[embedding.gid].extendEmbeddings(embedding.gid, embedding, extension);
			for(auto tembedding: tempEmbeddings){
				newEmbeddings.push_back(tembedding);
			}
		}
		gSpan(newCode, newEmbeddings);
	}
}

void test(clock_t t){
	cout<<"No of graphs="<<no_of_graphs<<endl;
	cout<<"Node Labels="<<maxNodeLabel+1<<endl;
	cout<<"Edge Labels="<<maxEdgeLabel+1<<endl;
	cout<<"Min sup="<<min_sup<<endl;
	cout<<"Node Labels sorted: ";
	for(auto label: nodeLabelOrder){
		cout<<label<<" ";
	}
	cout<<endl;
	cout<<"Edge Labels sorted: ";
	for(auto label: edgeLabelOrder){
		cout<<label<<" ";
	}
	cout<<endl;
	cout<<"Time taken: "<<(1.0*t)/(1.0*CLOCKS_PER_SEC)<<endl;
	cout<<"Frequent Subgraphs mined: "<<fsub<<endl;
}


int main(){
    freopen("debug.txt", "w", stdout);
    clock_t st_time=clock();
	find_number_of_graphs_and_labels();
	cerr<<"Scan 1 complete\n";
	find_frequent_labels();
	cerr<<"Scan 2 complete\n";
	constructGraphs();
	cerr<<"Scan 3 complete\n";
	int cnt;
	vector <Embedding> embeddings, tempEmbeddings;
	vector <DFSTuple> tuples;
	for(auto tuple: frequentTuples){
		DFSTuple dtuple=DFSTuple(0, 1, relabelledNodeLabels[tuple.XX.XX], relabelledEdgeLabels[tuple.XX.YY], relabelledNodeLabels[tuple.YY]);
		tuples.push_back(dtuple);
	}
	sort(tuples.begin(), tuples.end());
	for(auto tuple: tuples){
		embeddings.clear();
		cnt=0;
		for(auto graph: database){
			tempEmbeddings=graph.extendInitEdge(cnt, tuple.label_u, tuple.eLabel, tuple.label_v);
			cnt++;
			for(auto embedding: tempEmbeddings){
				embeddings.push_back(embedding);
			}
		}

		DFSCode code;
		code.tuples.push_back(tuple);
		if(!isMin(code)) continue;
		gSpan(code, embeddings);
		for(auto graph: database){
			graph.deleteTuple(tuple.label_u, tuple.eLabel, tuple.label_v);
		}
	}
	clock_t ed_time=clock();
	test(ed_time-st_time);
	return 0;
}
