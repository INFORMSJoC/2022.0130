//============================================================================
// Name        : IRMS.cpp
// Author      : 
// Version     :
// Copyright   : Your copyright notice
// Description : Instance Reduction based Memetic Search for node-weighted CNP
//============================================================================

#include <stdlib.h>
#include <math.h>
#include <fstream>
#include <iostream>
#include <unistd.h>
#include <time.h>
#include <string.h>
#include <limits.h>
#include <stack>
#include <queue>
#include <list>
using namespace std;

#define ADD(s,x,index_x,nbr_x)(x[nbr_x] = s,index_x[s] = nbr_x++)
#define EPS 0.000001
#define ALPHA 0.60
#define BETA 0.90
#define THETA 0.3
#define PS 5
#define MAX_IDLE_STEPS 1000

// running time
double StartTime,ImprovedTime,BestTime;
int FixedAllocatedSpace;
double LimitTime;
long unsigned BestNbrGens;

// instance
char *InstanceName; 			// instance file name
char *Dataset;					// data set
char ResultPath[100]; 			// result file path
char StatisticPath[100];		// statistical file path
char InstancePath[100];			// instance file path
char WeightPath[100];           // node weight file path
int NbrRepeats;

int NbrV,NbrE,Vnum;
int NbrC,ImprovedNbrC,BestNbrC;
int K; // maximum number of removed nodes
double W;		// knsapsack constraint
int *Node;
double *weight;
double SolWeight;
double ReducedWeight;

int **AdjacencyList;
//int *NbrAdjV;
int **Components,*VInComponent,*IndexVInComponent;
int *LargeComponentList;
int *RemovedV,*ImprovedRemovedV,*BestRemovedV,*ReducedV;
int *IndexRemovedV;
int NbrRemovedV,NbrImprovedRemovedV,NbrBestRemovedV,NbrReducedV;
int *List,*VList,*IndexVInVList;
bool *IsMarked;
int *UsedV;
int *VAge;
int *ReduceFlag;

int ObjValue,ImprovedObjValue,BestObjValue;
int BKV;	// best known value
bool OF;	// indicate the KBV is optimal or not

// Population
int **Pop;
double *PopCost;
double **SolSimilarity;
double *PopSimilarity;
double *PopScore;
int *PopSolSize;

// Tarjan
int *dfn;
int *low;
int *st_size;
int *cut_size;
double *impact;
int *flag;
bool *is_cut;
int time_stamp;
int root;
int Component;

/*list<int> *P;
int *d_num;
int *d;
double *rate;*/

void REMOVE(int s,int *x,int *index_x,int &nbr_x)
{
	register int *p0 = x;
	register int *p1 = &index_x[s];
	*(p0 + *p1) = *(p0 + (--nbr_x));
	*(index_x + *(p0 + nbr_x)) = *p1;
	*p1 = -1;
}

void dfs(int v,int *list)
{
	list[++list[0]] = v;
	IsMarked[v] = true;
	for(int i = 1; i <= AdjacencyList[v][0]; i++)
	{
		int w = AdjacencyList[v][i];
		if(IndexRemovedV[w] == -1 && !IsMarked[w])
			dfs(w,list);
	}
}

int depth_first_search(int v,int *list)
{
	list[0] = 0;
	for(int i = 0; i < NbrV; i++)
		IsMarked[Node[i]] = false;
	dfs(v,list);
	return list[0];
}

bool is_legal(int v)
{
	if(SolWeight + weight[v] > W)
		return false;
	else
		return true;
}

void tarjan_in_component(int x){
	dfn[x] = low[x] = ++time_stamp;
    int current_x = Components[Component][x];
    int *p = &AdjacencyList[current_x][1];
    for(int i = 1; i <= AdjacencyList[current_x][0]; i++,p++)
    {
    	int temp = *p;
    	if(IndexRemovedV[temp] == -1)
    	{
    		int index = IndexVInComponent[temp];
            if(!dfn[index]){         //not be visited
            	tarjan_in_component(index);
                low[x] = min(low[x], low[index]);
                if(dfn[x] < dfn[index])
                	st_size[x] = st_size[x] + st_size[index];
                if(low[index] >= dfn[x]) {   //if x is a cut node
                    flag[x]++;
            	    if(x != root)
            	    {
            		    is_cut[x] = true;
            		    cut_size[x] = cut_size[x] + st_size[index];
            		    impact[x] = impact[x] + (st_size[index]*(st_size[index]-1))/2;
            	    }
            	    else if(x == root && flag[x] > 1)
            	    	is_cut[x] = true;
                }
            }
            else
        	    low[x] = min(low[x], dfn[index]);
    	}
    }
}

// Sort the elements in the solution in am ascend order
void ascend_sort(int *sol, int size)
{
     int count = 0;
     memset(UsedV,0,FixedAllocatedSpace);

     for(int i = 0; i < size; i++)
    	 UsedV[sol[i]] = 1;

     for(int i = 0; i < NbrV; i++)
    	 if(UsedV[Node[i]] == 1)
    		 sol[count++] = Node[i];
}

// Check the solution is duplicate or not in the population
bool is_duplicate_sol(int index_sol)
{
    bool duplicate = false;
    for(int i = 0; i < index_sol; i++)
    {
    	if(PopSolSize[index_sol] != NbrImprovedRemovedV)
    		break;
    	duplicate = true;
    	for(int j = 0; j < NbrImprovedRemovedV; j++)
    		if(ImprovedRemovedV[j] != Pop[i][j])
    		{
    			duplicate = false;
    			break;
    		}

    	if(duplicate == true)
    		break;
    }
    return duplicate;
}

// Compute the distance between any two solutions in the population
double compute_SolSimilarity(int x1,int x2)
{
	double sol_similarity;
	int u = 0;
	int v = 0;
    int nbr_sharing_v = 0;
    while(u < PopSolSize[x1] && v < PopSolSize[x2])
    {
    	if(Pop[x1][u] == Pop[x2][v])
    	{
    		nbr_sharing_v++;
    		u++;
    		v++;
    	}
    	else if(Pop[x1][u] < Pop[x2][v])
    		u++;
        else if(Pop[x1][u] > Pop[x2][v])
        	v++;
    }
    sol_similarity = 2*(double)nbr_sharing_v/(double)(PopSolSize[x1]+PopSolSize[x2]);
    return sol_similarity;
}

void calculate_its_rank(int index,int nbr,double *x1,int *x2)
{
	double *x;
	x = new double[nbr];
	for(int i = 0; i < nbr; i++)
		x[i] = x1[i];

	int *flag;
	flag = new int[nbr];
	for(int i = 0; i < nbr; i++)
		flag[i] = 0;

	double temp;
    for(int i = 1; i < nbr; i++)
    	for(int j = nbr-1; j >= i; j--)
        {
    		if(index == 0)
    		{
    			// lower score, lower rank
    			if(x[j-1] > x[j])
    			{
    				temp = x[j-1];
    				x[j-1] = x[j];
    				x[j] = temp;
    			}
    		}
    		else if(index == 1)
    		{
    			// higher score, lower rank
    			if(x[j-1] < x[j])
    			{
    				temp = x[j-1];
    				x[j-1] = x[j];
    				x[j] = temp;
    			}
    		}
        }

    for(int i = 0; i < nbr; i++)
    	for(int j = 0; j < nbr; j++)
    	{
    		if(flag[j] == 0 && x1[i] == x[j])
    		{
    			x2[i] = j + 1;
    			flag[j] = 1;
    			break;
    		}
    	}
    delete [] x;
    delete [] flag;
}

/* Verify and store the results */
void store_result(char *result_file_path, int repeat)
{
	FILE *res;
	// Store the results
	if((res = fopen(result_file_path,"a+")) == NULL)
    {
		printf("Open failed for output  %s\n",result_file_path);
		exit(1);
    }
	fprintf(res,"   -----------------------------------------------------\n");
	fprintf(res,"   Repeat = %d\n",repeat);
	fprintf(res,"   -----------------------------------------------------\n");
	fprintf(res,"   best objective value = %d\n",BestObjValue);
	fprintf(res,"   time to find the best objective value = %f\n",BestTime);
	fprintf(res,"   number of generations to find the objective value = %ld\n",BestNbrGens);
	fprintf(res,"   Best removed nodes:\n");
	for(int i = 0; i < NbrBestRemovedV; i++)
		fprintf(res,"%d ",BestRemovedV[i]);
	fprintf(res,"\n");

	fclose(res);
}

/* Verify the results */
void check_result(int *removed_v,int nbr_removed_v,int obj_value,int nbr_c)
{
	int true_obj_value = 0;
	int true_nbr_c = 0;

	bool *is_visited;
	is_visited = new bool[NbrV];
	for(int i = 0; i < NbrV; i++)
		is_visited[i] = false;

	for(int i = 0; i < NbrV; i++)
		IndexRemovedV[i] = -1;
	for(int i = 0; i < nbr_removed_v; i++)
		IndexRemovedV[removed_v[i]] = 0;

	for(int i = 0; i < NbrV; i++)
		if(!is_visited[i] && IndexRemovedV[i] == -1)
		{
			depth_first_search(i,List);
			true_nbr_c++;
			for(int j = 1; j <= List[0]; j++)
				is_visited[List[j]] = true;
			true_obj_value += List[0]*(List[0]-1)/2;
		}

	if(nbr_c != true_nbr_c || true_obj_value != obj_value)
	{
		printf("The solution is not correct!\n");
		printf("nbr_c = %d, its true value = %d\n",nbr_c,true_nbr_c);
		printf("obj_value = %d, its true value = %d\n",obj_value,true_obj_value);
		exit(-1);
	}

	delete[] is_visited;

	// check knapsack constraint
	SolWeight = 0.0;
	for(int i = 0; i < nbr_removed_v; i++)
		SolWeight += weight[removed_v[i]];

	if(SolWeight > W + EPS)
	{
		printf("W = %lf, while the total weights of removed nodes is %lf\n",W,SolWeight);
		exit(-1);
	}
}

int select_remove_larger_component()
{
	int avg_c_size = int(float(NbrV-NbrRemovedV)/float(NbrC) + 0.5);
	if(avg_c_size < 2)
		avg_c_size = 2;

	int total_nbr_v_in_big_c = 0;
	LargeComponentList[0] = 0;
	for(int i = 0; i < NbrC; i++)
		if(Components[i][0] > avg_c_size)
		{
			LargeComponentList[++LargeComponentList[0]] = i;
			total_nbr_v_in_big_c += Components[i][0];
		}

	if(LargeComponentList[0] == 1)
	{
		if(rand()%2)
		{
			int best2C = 0,bestC = LargeComponentList[1];
			int max_size_c = Components[0][0];
			for(int i = 1; i < NbrC; i++)
				if(i != bestC && Components[i][0] > max_size_c)
				{
					max_size_c = Components[i][0];
					best2C = i;
				}
			return best2C;
		}
		else
			return LargeComponentList[1];
	}

	int index = rand()%total_nbr_v_in_big_c;
	int sum = 0,sum1 = Components[LargeComponentList[1]][0];
	for(int i = 1; i <= LargeComponentList[0]; i++)
	{
		if(index >= sum && index <= sum1)
			return LargeComponentList[i];
		sum = sum1;
		sum1 += Components[LargeComponentList[i+1]][0];
	}

	return LargeComponentList[LargeComponentList[0]];
}

// return a larger component
int select_remove_component()
{
	int min_size_c = NbrV,max_size_c = 0;
	if(NbrC > 50)
		return select_remove_larger_component();

	for(int i = 0; i < NbrC; i++)
		if(Components[i][0] > 2)
		{
			if(Components[i][0] < min_size_c)
				min_size_c = Components[i][0];
			if(Components[i][0] > max_size_c)
				max_size_c = Components[i][0];
		}
	float c_size_threshold = max_size_c-(max_size_c-min_size_c)*0.5-rand()%3;

	LargeComponentList[0] = 0;
	for(int i = 0; i < NbrC; i++)
		if(Components[i][0] >= c_size_threshold)
			LargeComponentList[++LargeComponentList[0]] = i;

	return LargeComponentList[rand()%LargeComponentList[0]+1];
}

// randomly select a node
int select_node_at_random()
{
	int x;
	while(1)
	{
		x = rand()%NbrV;
		if(IndexRemovedV[x] == -1 && is_legal(x))
			break;
	}
	return x;
}

// randomly select a node
int select_remove_node_at_random(int c)
{
	int index = rand()%Components[c][0] + 1;
	return Components[c][index];
}

int select_remove_node_with_weight(int c)
{
	int choose_v;
	int v;
	int *candidate_v;
	candidate_v = new int[NbrV];
	int nbr_candidate_v;
	int min_age = INT_MAX;

	for(int i = 1; i <= Components[c][0]; i++)
	{
		v = Components[c][i];
		if(VAge[v] < min_age)
		{
			min_age = VAge[v];
			candidate_v[0] = v;
			nbr_candidate_v = 1;
		}
		else if(VAge[v] == min_age)
		{
			candidate_v[nbr_candidate_v] = v;
			nbr_candidate_v++;
		}
	}
	choose_v = candidate_v[rand()%nbr_candidate_v];
	delete[] candidate_v;
	return choose_v;
}

int select_remove_node_with_impact(int c)
{
	int choose_v;
	int *best_v = new int[Components[c][0]+1];
	double min_impact = (double)INT_MAX;

	// Tarjan
	dfn = new int[Components[c][0]+1];
	low = new int[Components[c][0]+1];
	st_size = new int[Components[c][0]+1];
	cut_size = new int[Components[c][0]+1];
	impact = new double[Components[c][0]+1];
	flag = new int[Components[c][0]+1];
	is_cut = new bool[Components[c][0]+1];

	Component = c;
	time_stamp = 0;
	root = 1;
	for(int i = 1; i <= Components[c][0]; i++)
	{
	    dfn[i] = 0;
	    st_size[i] = 1;
	    cut_size[i] = 1;
	    impact[i] = 0.0;
	    flag[i] = 0;
	    is_cut[i] = false;
	}

	tarjan_in_component(root);
	best_v[0] = 0;
	for(int i = 1; i <= Components[c][0]; i++)
	{
		if(is_cut[i])
			impact[i] = impact[i] + (time_stamp-cut_size[i])*(time_stamp-cut_size[i]-1)/2;
		else
			impact[i] = impact[i] + (time_stamp-1)*(time_stamp-2)/2;

		impact[i] = impact[i] + NbrV * weight[Components[c][i]];
		if(abs(impact[i] - min_impact) < EPS)
			best_v[++best_v[0]] = i;
		else if(impact[i] < min_impact)
		{
			min_impact = impact[i];
			best_v[0] = 1;
			best_v[1] = i;
		}
	}
	choose_v = best_v[rand()%best_v[0]+1];

	delete[] best_v;
	// Tarjan
	delete[] dfn;
	delete[] low;
	delete[] st_size;
	delete[] cut_size;
	delete[] impact;
	delete[] flag;
	delete[] is_cut;
	return Components[c][choose_v];
}

int select_add_node()
{
	int v;
	int *add_node_list;
	add_node_list = new int[NbrV];
	bool *is_used_c;
	is_used_c = new bool[NbrV];
	long min_delta = NbrV*NbrV;
	int *p1 = RemovedV;
	add_node_list[0] = 0;
	for(int i = 0; i < NbrRemovedV; i++,p1++)
	{
		for(int i = 0; i < NbrC; i++)
			is_used_c[i] = false;

		int c_size = 0;
		int old_c_size = 0;
		int c1;
		int count = AdjacencyList[*p1][0],*p2 = &AdjacencyList[*p1][1];
		for(int i = 1; i <= count; i++, p2++)
			if(IndexRemovedV[*p2] == -1)
			{
				c1 = VInComponent[*p2];
				if(!is_used_c[c1])
				{
					c_size += Components[c1][0];
					old_c_size += Components[c1][0]*(Components[c1][0]-1)/2;
					is_used_c[c1] = true;
				}
			}

		c_size = c_size*(c_size+2)/2 - old_c_size;
		if(c_size < min_delta)
		{
			min_delta = c_size;
			add_node_list[0] = 1;
			add_node_list[1] = *p1;
		}
		else if(c_size == min_delta)
			add_node_list[++add_node_list[0]] = *p1;
	}

	if(add_node_list[0] == 0)
		v = RemovedV[rand()%NbrRemovedV];
	else
		v = add_node_list[rand()%add_node_list[0]+1];

	delete[] add_node_list;
	delete[] is_used_c;
	return v;
}

void create_a_component(int c,int *mlist,int *list)
{
	int index,*p = &list[1];
	if(Components[c] == NULL)
		Components[c] = new int [NbrV+1];
	Components[c][0] = 0;

	for(int i = 1; i <= list[0]; i++, p++)
	{
		Components[c][++Components[c][0]] = *p;
		IndexVInComponent[*p] = Components[c][0];
		VInComponent[*p] = c;

		index = IndexVInVList[*p];
		mlist[index] = mlist[mlist[0]--];
		IndexVInVList[mlist[index]] = index;
	}

	ObjValue += Components[c][0]*(Components[c][0]-1)/2;
}

void delete_a_component(int c)
{
	if(c == --NbrC)
		return;
	Components[c][0] = Components[NbrC][0];
	int *p1 = &Components[c][1];
	int *p2 = &Components[NbrC][1];
	int count = Components[NbrC][0];
	for(int i = 1; i <= count; i++,p1++,p2++)
	{
		*p1 = *p2;
		VInComponent[*p1] = c;
	}
}

void remove_node(int v)
{
	int index = IndexVInComponent[v];
	//int *p = &AdjacencyList[v][1];
	ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
	/*for(int i = 1; i <= AdjacencyList[v][0]; i++,p++)
		NbrAdjV[*p]--;*/

	int c = VInComponent[v];
	ObjValue -= Components[c][0]*(Components[c][0]-1)/2;

	int count = Components[c][0];
	VInComponent[v] = -1;
	if(--Components[c][0] == 0)
	{
		// Component is empty
		delete_a_component(c);
		return;
	}
	Components[c][index] = Components[c][count];
	IndexVInComponent[Components[c][index]] = index;

	if((depth_first_search(Components[c][1],List)) != Components[c][0])
	{
		//Component split has occurred
		count = VList[0] = Components[c][0];
		int *p1 = &VList[1],*p2 = &Components[c][1];
		for(int i = 1; i <= count; i++,p1++,p2++)
		{
			*p1 = *p2;
			IndexVInVList[*p1] = i;
		}

		// Rebuild the original component
		create_a_component(c,VList,List);

		// Built new component(s) with remaining vertices
		while(VList[0])
		{
			depth_first_search(VList[1],List);
			create_a_component(NbrC,VList,List);
			NbrC++;
		}
	}
	else
		ObjValue += Components[c][0]*(Components[c][0]-1)/2;
}

void add_node(int v)
{
	int index;
	REMOVE(v,RemovedV,IndexRemovedV,NbrRemovedV);
	int count = AdjacencyList[v][0],*p = &AdjacencyList[v][1];
	/*for(int i = 1; i <= count; i++,p++)
		NbrAdjV[*p]++;*/

	// Find component it should be in
	int c = -1;
	count = AdjacencyList[v][0];
	p = &AdjacencyList[v][1];
	for(int i = 1; i <= count; i++,p++)
		if(VInComponent[*p] != -1 && VInComponent[*p] != -2)
		{
			c = VInComponent[*p];
			break;
		}

	if(c != -1)
	{
		// Add to component of existing neighbor
		ObjValue -= Components[c][0]*(Components[c][0]-1)/2;

		index = Components[c][0] + 1;
		Components[c][0] = index;
		Components[c][index] = v;
		VInComponent[v] = c;
		IndexVInComponent[v] = index;

		if((depth_first_search(Components[c][1],List)) != Components[c][0])
		{
			// Need to combine components
			int *p1 = Components[c],*p2 = List;
			*(p1++) = *(p2++);
			int count = List[0];
			for(int i = 1; i <= count; i++,p1++,p2++)
			{
				*p1 = *p2;
				if(VInComponent[*p2] != c)
				{
					ObjValue -= Components[VInComponent[*p2]][0]*(Components[VInComponent[*p2]][0]-1)/2;
					Components[VInComponent[*p2]][0] = 0;
				}
				IndexVInComponent[*p2] = i;
				VInComponent[*p2] = c;
			}

			// delete all empty components
			for(int i = 0; i < NbrC; i++)
				if(Components[i][0] == 0)
				{
					delete_a_component(i);
					i--;
				}
		}
		ObjValue += Components[c][0]*(Components[c][0]-1)/2;
	}
	else
	{
		// New single node component
		if(Components[NbrC] == NULL)
			Components[NbrC] = new int [NbrV+1];

		Components[NbrC][0] = 1;
		Components[NbrC][1] = v;
		IndexVInComponent[v] = 1;
		VInComponent[v] = NbrC++;
	}
}

void read_instance(const char *filename)
{
	ifstream FIC(filename);
    if(!FIC.is_open())
    {
    	cout << "***: Cannot open the file: " << InstanceName << endl;
    	exit(0);
    }

	FIC >> NbrV;
	//Vnum = NbrV;
	if(FIC.eof())
	{
		cout << "###: Cannot open the file: " << InstanceName << endl;;
    	exit(-1);
	}

	AdjacencyList = new int *[NbrV];
	Node = new int[NbrV];

	int *temp = new int[NbrV+1];
	NbrE = 0;
	for(int i = 0; i < NbrV; i++)
	{
		int v1,v2;
		FIC >> v1;
		Node[i] = i;

		for(int c = FIC.get(); c != ':' && isspace(c); c = FIC.get());
		bool nextLine = false;

		temp[0] = 0;
		while(!FIC.eof() && !nextLine)
		{
			while(isspace(FIC.peek()))
				nextLine = (FIC.get()=='\n');

			if(!nextLine)
			{
				FIC >> v2;
				temp[++temp[0]] = v2;
				NbrE++;
			}
		}

		// adjacency node list
		AdjacencyList[v1] = new int [temp[0]+1];
		for(int i = 0; i <= temp[0]; i++)
		{
			AdjacencyList[v1][i] = temp[i];
		}
	}

    FIC.close();

	NbrE /= 2;
	delete temp;
}

void read_large_instance(const char *filename)
{
	ifstream FIC(filename);
    if(!FIC.is_open())
    {
    	cout << "***: Cannot open the file: " << InstanceName << endl;
    	exit(0);
    }

    int rows,colomns;
	FIC >> rows >> colomns >> NbrE;
	NbrV = rows > colomns ? rows : colomns;
	if(FIC.eof())
	{
		cout << "###: Cannot open the file: " << InstanceName << endl;;
    	exit(-1);
	}

	AdjacencyList = new int *[NbrV];
	for(int i = 0; i < NbrV; i++)
		AdjacencyList[i] = new int[NbrV+1];
	Node = new int[NbrV];
	for(int i = 0; i < NbrV; i++)
		AdjacencyList[i][0] = 0;

	int v1,v2,temp1,temp2;
	double temp3;
	for(int i = 0; i < NbrV; i++)
	{
		FIC >> temp1 >> temp2 >> temp3;
		if(temp1 == temp2)
			continue;
		v1 = temp1 - 1;
		v2 = temp2 - 1;
		Node[i] = i;

		// adjacency node list
		AdjacencyList[v1][++AdjacencyList[v1][0]] = v2;
		AdjacencyList[v2][++AdjacencyList[v2][0]] = v1;
	}
    FIC.close();
}

void generate_weight(const char *filename)
{
	ofstream FIC(filename);
    if(!FIC)
    {
    	cout << "***: Cannot open the weight file of: " << InstanceName << endl;
    	exit(0);
    }

    double min = 0.2, max = 3.0;
    double weight;
    srand((unsigned int)time(NULL));
    for(int i = 0; i < NbrV; i++)
    {
    	weight = min + ((double)rand()/RAND_MAX)*(max-min);
		FIC << weight << endl;
    }
    FIC.close();
}

void read_weight(const char *filename)
{
	ifstream FIC(filename);
    if(!FIC.is_open())
    {
    	cout << "***: Cannot open the weight file of: " << InstanceName << endl;
    	exit(0);
    }

    weight = new double[NbrV];
    double w;
    for(int i = 0; i < NbrV; i++)
    {
		FIC >> w;
		weight[i] = w;
    }
    FIC.close();
}

void setup_data()
{
	FixedAllocatedSpace = NbrV*sizeof(int);
	Components = new int * [NbrV];
	for(int i = 0; i < NbrV; i++)
		Components[i] = new int[NbrV+1];

	VInComponent = new int [NbrV];
	IndexVInComponent = new int [NbrV];
	LargeComponentList = new int [NbrV];
	List = new int [NbrV+1];
	VList = new int [NbrV+1];
	IndexVInVList = new int [NbrV];
	RemovedV = new int [NbrV];
	IndexRemovedV = new int [NbrV];
	ImprovedRemovedV = new int[NbrV];
	BestRemovedV = new int [NbrV];
	UsedV = new int[NbrV];
	IsMarked = new bool [NbrV];
	VAge = new int[NbrV];
	ReducedV = new int[NbrV];

	// Population
	Pop = new int*[PS+1];
	for(int i = 0; i < PS+1; i++)
		Pop[i] = new int[NbrV];
	PopCost = new double[PS+1];
	SolSimilarity = new double*[PS+1];
	for(int i = 0; i < PS+1; i++)
		SolSimilarity[i] = new double[PS+1];
	PopSimilarity = new double[PS+1];
	PopScore = new double[PS+1];
	PopSolSize = new int[PS+1];
}

void clear_data()
{
	for(int i = 0; i < NbrV; i++)
		delete Components[i];

	delete[] VInComponent;
	delete[] IndexVInComponent;
	delete[] LargeComponentList;
	delete[] List;
	delete[] VList;
	delete[] IndexVInVList;
	delete[] RemovedV;
	delete[] IndexRemovedV;
	delete[] ImprovedRemovedV;
	delete[] BestRemovedV;
	delete[] UsedV;
	delete[] IsMarked;
	delete[] VAge;
	delete[] ReducedV;

    //betweenness centrality
	/*delete[] CB;
	delete[] P;
	delete[] d_num;
	delete[] d;
	delete[] rate;*/

	// population
	delete[] PopCost;
	delete[] PopSimilarity;
	delete[] PopScore;
	delete[] PopSolSize;
	for(int i = 0; i < PS+1; i++)
	{
		delete Pop[i];
		delete SolSimilarity[i];
	}
}

void update_improved_sol()
{
	ImprovedTime = (clock() - StartTime)/CLOCKS_PER_SEC;
	ImprovedObjValue = ObjValue;
	ImprovedNbrC = NbrC;
	NbrImprovedRemovedV = NbrRemovedV;
	for(int i = 0; i < NbrRemovedV; i++)
		ImprovedRemovedV[i] = RemovedV[i];
}

void update_best_sol()
{
	BestTime = ImprovedTime;
	BestObjValue = ImprovedObjValue;
	BestNbrC = ImprovedNbrC;
	NbrBestRemovedV = NbrImprovedRemovedV;
	for(int i = 0; i < NbrImprovedRemovedV; i++)
		BestRemovedV[i] = ImprovedRemovedV[i];
}

// construct a random solution
void random_construct_sol()
{
	int v;
	int index;
	int *candidate_v;
	candidate_v = new int[NbrV];
	int nbr_candidate_v = 0;

	for(int i = 0; i < NbrV; i++)
	{
		candidate_v[nbr_candidate_v] = Node[i];
		nbr_candidate_v++;
	}
	memset(UsedV,0,FixedAllocatedSpace);

	NbrRemovedV = 0;
	SolWeight = 0.0;
	while(1)
	{
		//srand((unsigned)time(NULL));
		index = rand()%nbr_candidate_v;
		v = candidate_v[index];
	    nbr_candidate_v--;
	    candidate_v[index] = candidate_v[nbr_candidate_v];

		// check the knapsack constraint
		if(SolWeight + weight[v] > W)
			break;

	    UsedV[v] = 1;
	    VInComponent[v] = -1;
	    IndexVInComponent[v] = -1;
	    ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
	    SolWeight += weight[v];
	}

	int count = 0;
	for(int i = 0; i < NbrV; i++)
		if(UsedV[Node[i]] == 0)
		{
			VInComponent[Node[i]] = -1;
			IndexVInComponent[Node[i]] = -1;
			IndexRemovedV[Node[i]] = -1;
			count++;
			VList[count] = Node[i];
			IndexVInVList[Node[i]] = count;
		}
	VList[0] = NbrV - NbrRemovedV;

	NbrC = 0;
	ObjValue = 0;
	while(VList[0])
	{
		depth_first_search(VList[1],List);
		create_a_component(NbrC,VList,List);
		NbrC++;
	}
	delete[] candidate_v;
}

/* two-stages neighborhood search procedure */
void CBNS_procedure()
{
	long nbr_step = 0;
	long nbr_idle_steps = 0;
	int c,v;
	/*for(int i = 0; i < NbrV; i++)
		VAge[Node[i]] = 0;*/

	ImprovedObjValue = INT_MAX;
	while(nbr_idle_steps < MAX_IDLE_STEPS)
	{
		nbr_step++;
		// Remove a node from G
		c = select_remove_component();	// select a larger component
		v = select_remove_node_with_weight(c);	// randomly remove a node from selected component
		remove_node(v);
		VAge[v] = nbr_step;
		SolWeight += weight[v];

		// Add a node back to G
		while(SolWeight > W)
		{
			v = select_add_node();
			add_node(v);	//  add a node to G which gives the minimum increase in f
			SolWeight -= weight[v];
			VAge[v] = nbr_step;
		}

		// Update the best solution
		if(ObjValue < ImprovedObjValue)
		{
			update_improved_sol();
			nbr_idle_steps = 0;
		}
		else
			nbr_idle_steps++;

		if((clock()-StartTime)/CLOCKS_PER_SEC >= LimitTime)
			break;
	}
}

void CHNS_procedure()
{
	long nbr_step = 0;
	long nbr_idle_steps = 0;
	int c,v;
	for(int i = 0; i < NbrV; i++)
		VAge[Node[i]] = 0;

	ImprovedObjValue = INT_MAX;
	while(nbr_idle_steps < MAX_IDLE_STEPS)
	{
		nbr_step++;
		// Remove a node from G
		int destroy_num = 5;
	    while(destroy_num > 0)
	    {
	    	destroy_num--;
			// Remove a node from G
			c = select_remove_component();	// select a larger component
		    double ns = (double)rand()/RAND_MAX;
			if(ns < THETA)
			    v = select_remove_node_with_impact(c);
			else
			    v = select_remove_node_with_weight(c);	// randomly remove a node from selected component
			remove_node(v);
			VAge[v] = nbr_step;
			SolWeight += weight[v];
	    }

		// Add a node back to G
		while(SolWeight > W)
		{
			v = select_add_node();
			add_node(v);	//  add a node to G which gives the minimum increase in f
			SolWeight -= weight[v];
			VAge[v] = nbr_step;
		}

		// Update the best solution
		if(ObjValue < ImprovedObjValue)
		{
			update_improved_sol();
			nbr_idle_steps = 0;
		}
		else
			nbr_idle_steps++;

		if((clock()-StartTime)/CLOCKS_PER_SEC >= LimitTime)
			break;
	}
}


/* Population initialization procedure */
void build_population()
{
	int swap_out_v,swap_in_v;
	int nbr_sol = 0;
	int true_nbr_sol = 0;
	//srand((unsigned)time(NULL));
	while(nbr_sol < PS)
	{
		//srand((unsigned)time(NULL));
		true_nbr_sol++;

		// generate an initial solution
		random_construct_sol();
		update_improved_sol();

		// improve it by a neighborhood search procedure
		CBNS_procedure();
		ascend_sort(ImprovedRemovedV, NbrImprovedRemovedV);

    	// update the best solution
    	if(ImprovedObjValue < BestObjValue)
    	{
    		update_best_sol();
    	}

    	// check the time limit
    	if((clock()-StartTime)/CLOCKS_PER_SEC >= LimitTime)
    		return;

		// modify the improved solution
		int is_update = 1;
		int count = 0;
		int flag;
		while(is_duplicate_sol(nbr_sol) == true)
        {
			if(is_update == 1)
			{
				memset(UsedV,0,FixedAllocatedSpace);
				for(int i = 0; i < NbrImprovedRemovedV; i++)
					UsedV[ImprovedRemovedV[i]] = 1;

				NbrRemovedV = 0;
				SolWeight = 0.0;
				for(int i = 0; i < NbrV; i++)
					if(UsedV[Node[i]] == 1)
					{
						VInComponent[Node[i]] = -1;
						IndexVInComponent[Node[i]] = -1;
						ADD(Node[i],RemovedV,IndexRemovedV,NbrRemovedV);
						SolWeight += weight[Node[i]];
					}
					else
					{
						VInComponent[Node[i]] = -1;
						IndexVInComponent[Node[i]] = -1;
						IndexRemovedV[Node[i]] = -1;
						count++;
						VList[count] = Node[i];
						IndexVInVList[Node[i]] = count;
					}
				VList[0] = NbrV - NbrRemovedV;
				NbrC = 0;
				ObjValue = 0;
				while(VList[0])
				{
					depth_first_search(VList[1],List);
					create_a_component(NbrC,VList,List);
					NbrC++;
				}
				is_update = 0;
			}

			// add a vertex back to G
			swap_out_v = select_add_node();
			add_node(swap_out_v);

			// remove a vertex from G
			flag = 0;
			while(flag == 0)
			{
				swap_in_v = Node[rand()%NbrV];
				if(VInComponent[swap_in_v] != -1 && is_legal(swap_in_v))
					break;
			}
			remove_node(swap_in_v);

			update_improved_sol();
			ascend_sort(ImprovedRemovedV, NbrImprovedRemovedV);
        }

    	// insert it into the population
    	PopCost[nbr_sol] = ImprovedObjValue;
    	PopSolSize[nbr_sol] = NbrImprovedRemovedV;
    	for(int i = 0; i < NbrImprovedRemovedV; i++)
    		Pop[nbr_sol][i] = ImprovedRemovedV[i];
    	nbr_sol++;
	}

	// evaluate all individuals in the population
    for(int i = 0; i < PS; i++)
    {
    	for(int j = i + 1; j < PS; j++)
    	{
    		SolSimilarity[i][j] = compute_SolSimilarity(i,j);
    		SolSimilarity[j][i] = SolSimilarity[i][j];
    	}
    	SolSimilarity[i][i] = 1.0;
    }
}

/* update the pool */
bool update_population()
{
	bool is_updated = false;
	// insert the offspring solution into the population
	PopCost[PS] = ImprovedObjValue;
	PopSolSize[PS] = NbrImprovedRemovedV;
	for(int i = 0; i < NbrImprovedRemovedV; i++)
		Pop[PS][i] = ImprovedRemovedV[i];

    for(int i = 0; i < PS+1; i++)
    {
    	SolSimilarity[i][PS] = compute_SolSimilarity(i,PS);
    	SolSimilarity[PS][i] = SolSimilarity[i][PS];
    }
    SolSimilarity[PS][PS] = 1.0;

    // Calculate the average distance of each individual with the whole population
    for(int i = 0; i < PS+1; i++)
    {
    	PopSimilarity[i] = 0.0;
    	for(int j = 0; j < PS+1; j++)
    		if(j != i)
    			PopSimilarity[i] += SolSimilarity[i][j];

    	PopSimilarity[i] = PopSimilarity[i]/PS;
    }

    int *cost_rank,*distance_rank;
    cost_rank = new int[PS+1];
    distance_rank = new int[PS+1];

    for(int i = 0; i < PS+1; i++)
    {
    	cost_rank[i] = i + 1;
    	distance_rank[i] = i + 1;
    }

    calculate_its_rank(1,PS+1,PopCost,cost_rank);
    calculate_its_rank(1,PS+1,PopSimilarity,distance_rank);

    // Compute the score of each individual in the population
    for(int i = 0; i < PS+1; i++)
    	PopScore[i] = ALPHA*((double) cost_rank[i]) + (1.0-ALPHA)*((double) distance_rank[i]);

    // find out the worst solution
    double min_score = (double)INT_MAX;
    int index_worst_sol;
    for(int i = 0; i < PS+1; i++)
    	if(PopScore[i] < min_score)
    	{
    		min_score = PopScore[i];
    		index_worst_sol = i;
    	}

	// replace the worst solution if condition is met.
    if(index_worst_sol != PS && is_duplicate_sol(PS) == false)
    {
    	is_updated = true;

    	//update pop
    	PopCost[index_worst_sol] = PopCost[PS];
    	PopSolSize[index_worst_sol] = PopSolSize[PS];
        for(int i = 0; i < PopSolSize[PS]; i++)
        	Pop[index_worst_sol][i] = Pop[PS][i];

        // update sol_distance
        for(int i = 0; i < PS; i++)
        	if(i != index_worst_sol)
        	{
        		SolSimilarity[i][index_worst_sol] = SolSimilarity[PS][i];
        		SolSimilarity[index_worst_sol][i] = SolSimilarity[PS][i];
        	}
        	else
        		SolSimilarity[index_worst_sol][index_worst_sol] = 1.0;

        for(int i = 0; i < PS; i++)
        {
        	PopSimilarity[i] = 0.0;
        	for(int j = 0; j < PS+1; j++)
        		if(j != i)
        			PopSimilarity[i] += SolSimilarity[i][j];

        	PopSimilarity[i] = PopSimilarity[i]/PS;
        }
     }
    delete[] cost_rank;
    delete[] distance_rank;
    return is_updated;
}

void pattern_guided_instance_reduction()
{
	int ID1, ID2;
	// randomly select two solutions
    ID1 = rand()%PS;
    while(1)
    {
    	ID2 = rand()%PS;
    	if(ID2 != ID1)
    	    break;
    }
	memset(UsedV,0,FixedAllocatedSpace);
	// find the common nodes
	for(int i = 0; i < PopSolSize[ID1]; i++)
	{
    	UsedV[Pop[ID1][i]]++;
	}
    for(int i = 0; i < PopSolSize[ID2]; i++)
    {
    	UsedV[Pop[ID2][i]]++;
    }

	int NodeNum = 0;
	NbrReducedV = 0;
	ReducedWeight = 0;
	// reduce an instance based on sharing nodes
	for(int i = 0; i < NbrV; i++)
	{
		double r = (double)rand()/RAND_MAX;
		if(UsedV[Node[i]] == 2 && r < BETA)
		{
		    ReducedV[NbrReducedV++] = Node[i];
		    VInComponent[Node[i]] = -2;
		    IndexVInComponent[Node[i]] = -2;
		    IndexRemovedV[Node[i]] = -2;
		    ReducedWeight += weight[Node[i]];
		     /*int *p = &AdjacencyList[Node[i]][1];
		   for(int i = 1; i <= AdjacencyList[Node[i]][0]; i++,p++)
		   		NbrAdjV[*p]--;*/
		}
		else
			Node[NodeNum++] = Node[i];
	}

	//cout << ReducedWeight << "," << (double)ReducedWeight/W << "," << (double)NbrReducedV/NbrV << endl;
	W = W - ReducedWeight;
	NbrV = NbrV - NbrReducedV;
}

void expand_solution()
{
	W = W + ReducedWeight;
	NbrV = NbrV + NbrReducedV;
	for(int i = 0; i < NbrReducedV; i++)
	{
		ADD(ReducedV[i],RemovedV,IndexRemovedV,NbrRemovedV);
	    VInComponent[ReducedV[i]] = -1;
	    IndexVInComponent[ReducedV[i]] = -1;
	    SolWeight += weight[ReducedV[i]];
	}
	update_improved_sol();

	for(int i = 0; i < NbrV; i++)
		Node[i] = i;
}

void determine_model_K_and_BKV(char*filename)
{
	if(strcmp(filename,"BarabasiAlbert_n500m1.txt") == 0)
	{
		K = 50;
		BKV = 195;
		OF = true;
	}
	else if(strcmp(filename,"BarabasiAlbert_n1000m1.txt") == 0)
	{
		K = 75;
		BKV = 558;
		OF = true;
	}
	else if(strcmp(filename,"BarabasiAlbert_n2500m1.txt") == 0)
	{
		K = 100;
		BKV = 3704;
		OF = true;
	}
	else if(strcmp(filename,"BarabasiAlbert_n5000m1.txt") == 0)
	{
		K = 150;
		BKV = 10196;
		OF = true;
	}
	else if(strcmp(filename,"ErdosRenyi_n235.txt") == 0)
	{
		K = 50;
		BKV = 295;
		OF = true;
	}
	else if(strcmp(filename,"ErdosRenyi_n466.txt") == 0)
	{
		K = 80;
		BKV = 1524;
		OF = true;
	}
	else if(strcmp(filename,"ErdosRenyi_n941.txt") == 0)
	{
		K = 140;
		BKV = 5012;
		OF = true;
	}
	else if(strcmp(filename,"ErdosRenyi_n2344.txt") == 0)
	{
		K = 200;
		BKV = 902498;
		OF = false;
	}
	else if(strcmp(filename,"ForestFire_n250.txt") == 0)
	{
		K = 50;
		BKV = 194;
		OF = true;
	}
	else if(strcmp(filename,"ForestFire_n500.txt") == 0)
	{
		K = 110;
		BKV = 257;
		OF = true;
	}
	else if(strcmp(filename,"ForestFire_n1000.txt") == 0)
	{
		K = 150;
		BKV = 1260;
		OF = true;
	}
	else if(strcmp(filename,"ForestFire_n2000.txt") == 0)
	{
		K = 200;
		BKV = 4545;
		OF = true;
	}
	else if(strcmp(filename,"WattsStrogatz_n250.txt") == 0)
	{
		K = 70;
		BKV = 3083;
		OF = true;
	}
	else if(strcmp(filename,"WattsStrogatz_n500.txt") == 0)
	{
		K = 125;
		BKV = 2072;
		OF = true;
	}
	else if(strcmp(filename,"WattsStrogatz_n1000.txt") == 0)
	{
		K = 200;
		BKV = 109677;
		OF = false;
	}
	else if(strcmp(filename,"WattsStrogatz_n1500.txt") == 0)
	{
		K = 265;
		BKV = 13098;
		OF = true;
	}
	else
	{
		printf("Error occurs in determining K and BKV value of model instance!\n");
	}
}

void determine_realworld_K_and_BKV(char*filename)
{
	if(strcmp(filename,"Bovine.txt") == 0)
	{
		K = 3;
		BKV = 268;
		OF = true;
	}
	else if(strcmp(filename,"Circuit.txt") == 0)
	{
		K = 25;
		BKV = 2099;
		OF = true;
	}
	else if(strcmp(filename,"Ecoli.txt") == 0)
	{
		K =15;
		BKV = 806;
		OF = true;
	}
	else if(strcmp(filename,"USAir97.txt") == 0)
	{
		K = 33;
		BKV = 4336;
		OF = true;
	}
	else if(strcmp(filename,"humanDiseasome.txt") == 0)
	{
		K = 52;
		BKV = 1115;
		OF = true;
	}
	else if(strcmp(filename,"Treni_Roma.txt") == 0)
	{
		K = 26;
		BKV = 918;
		OF = true;
	}
	else if(strcmp(filename,"EU_flights.txt") == 0)
	{
		K = 119;
		BKV = 348268;
		OF = true;
	}
	else if(strcmp(filename,"openflights.txt") == 0)
	{
		K = 186;
		BKV = 26783;
		OF = false;
	}
	else if(strcmp(filename,"yeast1.txt") == 0)
	{
		K = 202;
		BKV = 1412;
		OF = true;
	}
	else if(strcmp(filename,"Hamilton1000.txt") == 0)
	{
		K = 100;
		BKV = 306349;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton2000.txt") == 0)
	{
		K = 200;
		BKV = 1242739;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton3000a.txt") == 0)
	{
		K = 300;
		BKV = 2840690;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton3000b.txt") == 0)
	{
		K = 300;
		BKV = 2837584;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton3000c.txt") == 0)
	{
		K = 300;
		BKV = 2835369;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton3000d.txt") == 0)
	{
		K = 300;
		BKV = 2828492;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton3000e.txt") == 0)
	{
		K = 300;
		BKV = 2843000;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton4000.txt") == 0)
	{
		K = 400;
		BKV = 5038611;
		OF = false;
	}
	else if(strcmp(filename,"Hamilton5000.txt") == 0)
	{
		K = 500;
		BKV = 7964765;
		OF = false;
	}
	else if(strcmp(filename,"powergrid.txt") == 0)
	{
		K = 494;
		BKV = 15862;
		OF = false;
	}
	else if(strcmp(filename,"OClinks.txt") == 0)
	{
		K = 190;
		BKV = 611253;
		OF = false;
	}
	else if(strcmp(filename,"facebook.txt") == 0)
	{
		K = 404;
		BKV = 420334;
		OF = false;
	}
	else if(strcmp(filename,"grqc.txt") == 0)
	{
		K = 524;
		BKV = 13591;
		OF = false;
	}
	else if(strcmp(filename,"hepth.txt") == 0)
	{
		K = 988;
		BKV = 106276;
		OF = false;
	}
	else if(strcmp(filename,"hepph.txt") == 0)
	{
		K = 1201;
		BKV = 6155877;
		OF = false;
	}
	else if(strcmp(filename,"astroph.txt") == 0)
	{
		K = 1877;
		BKV = 53963375;
		OF = false;
	}
	else if(strcmp(filename,"condmat.txt") == 0)
	{
		K = 2313;
		BKV = 2298596;
		OF = false;
	}
	else
	{
		printf("Error occurs in determining K and BKV value of real-world instance!\n");
	}
}

void reduce_solve_combine()
{
	// Step1. reduce instance based on common pattern
	pattern_guided_instance_reduction();

	// Step2. solve the reduced instance by a local search
	random_construct_sol();
	update_improved_sol();
	CHNS_procedure();

	// Step3. expand the solution for the original instance
	expand_solution();
	// update the best solution
	if(ImprovedObjValue < BestObjValue)
	{
		ascend_sort(ImprovedRemovedV, NbrImprovedRemovedV);
		update_best_sol();
	}
}

void Instance_Reduction_Based_Search_CNP()
{
	int nbr_gens, nbr_idle_gens;
	StartTime = clock();
	BestObjValue = INT_MAX;
	nbr_gens = 0;
	nbr_idle_gens = 0;

	/* Step1. Population initialization */
	build_population();

	//Population Evolution
	while((clock()-StartTime)/CLOCKS_PER_SEC < LimitTime)
	{
		/* Step2. Reduce instance and resolve the instance */
	    reduce_solve_combine();

		/* Step3. Search around the expanded solution */
	    CHNS_procedure();
		ascend_sort(ImprovedRemovedV, NbrImprovedRemovedV);
	    nbr_gens++;

        /* Record the best solution */
	    if(ImprovedObjValue < BestObjValue)
	    {
	        update_best_sol();
	        BestNbrGens = nbr_gens;
	        nbr_idle_gens = 0;
	    }
    	else
    		nbr_idle_gens++;

	    /* Step4. Update Population */
	    update_population();
	}
}

int main(int argc, char **argv)
{
	FILE *sum;
	int succ_times;
	if(argc == 5)
    {
		InstanceName = argv[1];
		Dataset = argv[2];
		LimitTime = atof(argv[3]);
		NbrRepeats = atoi(argv[4]);
    }
    else
    {
        cout << endl << "### Input the following parameters ###" << endl;
        cout << "Instance name, data set, time limit and number of repeats" << endl;
        exit(0);
    }

	// determine the K and BKV for a given instance
	if(strcmp(Dataset,"model") == 0)
		determine_model_K_and_BKV(InstanceName);
	else if(strcmp(Dataset,"realworld") == 0)
		determine_realworld_K_and_BKV(InstanceName);
	W = (double)K;

	// instance file path
	strcpy(InstancePath,"./instances/");
    strcat(InstancePath,Dataset);
    strcat(InstancePath,"/");
	strcat(InstancePath,InstanceName);

	// result file path of each run
    strcpy(ResultPath,"./results/");
    strcat(ResultPath,Dataset);
    strcat(ResultPath,"/");
    strcat(ResultPath,InstanceName);
    strcat(ResultPath,"_res.out");

	// statistical file path over multiple runs
    strcpy(StatisticPath,"./results/");
    strcat(StatisticPath,Dataset);
    strcat(StatisticPath,"/");
    strcat(StatisticPath,InstanceName);
    strcat(StatisticPath,"_sum.out");

	// weight file path
    strcpy(WeightPath,"./weights/");
    strcat(WeightPath,Dataset);
    strcat(WeightPath,"/");
    strcat(WeightPath,InstanceName);
    strcat(WeightPath,"_weight.txt");

	if((sum = fopen(StatisticPath,"a+")) == NULL)
    {
		printf("Open failed for output  %s\n",StatisticPath);
		exit(1);
    }

	// read an instance
	read_instance(InstancePath);
	read_weight(WeightPath);

	cout << "Instance: " << InstanceName << endl;
	cout << "nbr_v = " << NbrV << ", nbr_e = " << NbrE << endl;
	cout << "Parameters: K = " << K << endl;

	int min_value = INT_MAX;
	double avg_value = 0.0;
	double avg_time = 0.0;
	double avg_gens = 0.0;

	// repeatedly run the algorithm
	fprintf(sum,"Instance: %s and Limit time = %f\n",InstanceName,LimitTime);
	fprintf(sum,"---------------------------------------------------------\n");
	fprintf(sum,"Repeat, BestObjValue, BestTime, BestSteps, BestGens\n");
	for(int i = 0; i < NbrRepeats; i++)
	{
		// Clear and initialize
		srand((unsigned)time(NULL));
		setup_data();

		/*********************************************************************************************/
		// Invoke the proposed algorithm to solve the instance
		Instance_Reduction_Based_Search_CNP();

		// Check and store the found best solution
		store_result(ResultPath,i+1);
		check_result(BestRemovedV,NbrBestRemovedV,BestObjValue,BestNbrC);

		/*********************************************************************************************/
		if(BestObjValue < min_value)
		{
			min_value = BestObjValue;
			succ_times = 1;
		}
		else if(BestObjValue == min_value)
			succ_times++;

		avg_value += BestObjValue;
		avg_time += BestTime;
		avg_gens += BestNbrGens;
		fprintf(sum,"%d,%d,%.3lf,%ld\n",i+1,BestObjValue,BestTime,BestNbrGens);
		printf("Repeat = %d, BestObjValue = %d, BestTime = %lf, BestGens = %ld\n",i+1,BestObjValue,BestTime,BestNbrGens);
		clear_data();
	}

	avg_value = avg_value/double(NbrRepeats);
	avg_time = avg_time/double(NbrRepeats);
	avg_gens = avg_gens/double(NbrRepeats);
	fprintf(sum,"---------------------------------------------------------\n");
	fprintf(sum,"%d,%.3lf,%.3lf,%.3lf\n",succ_times,avg_value,avg_time,avg_gens);
	fprintf(sum,"---------------------------------------------------------\n");
	fclose(sum);
	cout << "best value = " << min_value << ", average value = " << avg_value << ", average time = " << avg_time << ", succ times = " << succ_times << endl;

	FILE *out;
	char final_result_file[100];
    strcpy(final_result_file,Dataset);
	strcat(final_result_file,"_IRMS_NWCNP_result.csv");
	out = fopen(final_result_file,"at+");
	if(out != NULL)
	{
		fprintf(out,"%s, %d, %d, %f, %f, %f, %d\n",InstanceName,BKV,min_value,avg_value,avg_time,avg_gens,succ_times);
	}
	fclose(out);

	delete[] Node;
	delete[] weight;
	for(int i = 0; i < NbrV; i++)
	{
		delete AdjacencyList[i];
	}
	return 0;
}
