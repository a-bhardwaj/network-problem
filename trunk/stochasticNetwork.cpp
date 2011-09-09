// -------------------------------------------------------------- -*- C++ -*-
// File: stochasticNetwork.cpp
// @author: Avinash Bhardwaj
// --------------------------------------------------------------------------
// Property of Berkeley Computational Optimization Group,
// University of California, Berkeley
// --------------------------------------------------------------------------
//
// stochasticNetwork.cpp -	Performance testing of the adding extended pack
//							inequalities against the CPLEX 12.3 standard and
//							outer approximation procedures for network flow 
//							problem with probabilistic capacities.

/*
REMARK :					To check if an array contains integers do 
							arrayName.areElementsInteger();

REMARK :					Never use IloCplex::getCplexTime() to measure solve
							time. It returns the time elapsed since the start of
							the application and thus will keep increasing.

REMARK :					As soon as you apply any control callbacks cplex by 
							default turn offs the parallel processing of the nodes 
							to avoid any logical misinterpretation. This can be 
							turned back again by threads Parameter of the IloCplex 
							Object For eg: IloCplex::setParam((IloCplex::Threads, N)), 
							where N is the minimum of the number of parallel licences 
							available and number of parallel processing threads on 
							the machine. For more information refer to Parameters Manual 
							of your CPLEX version for Parameter name 
							"global default thread count"
*/

#include <ilcplex/ilocplex.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h> 
#include <math.h>

//@var		rootRelaxationObjValue	:	To store the objective value of the root relaxation.

IloNum sepObjValue;
static IloInt cutsAdded = 0;

ILOSTLBEGIN

#define EPSILON 1e-4
#define EPS 1e-7
#define TIM_LIM 1800

typedef IloArray<IloIntArray>    IntMatrix;
typedef IloArray<IloNumVarArray> NumVarMatrix;

//@method	usage					:	To specify the usage error
static void 
	usage (const char *progname) {
		cerr << "Usage: " << progname << " <Output File> -a <AlgoType>" << endl;
		cerr << "      <Output File>          Output file to summarize the computation results. (Default: Same name as input file)" << endl;
		cerr << "      <AlgoType>	          The type of cover algorithm to use, 0: Conic Cuts, 1: Linearized Cuts, 2: Extended Pack Inequalities. (Default: 0)" << endl << endl;
		cerr << " Exiting..." << endl;
} // END usage


bool FileExists(const char *strFilename) {
	FILE* fp = fopen(strFilename, "r");
	bool exists = false;
	if (fp) {
		// file exists
		exists = true;
		fclose(fp);
	} 
	
	return exists;
}

//@method	findIndices				:	To find indices of the TRUE enteries of a binary array
IloIntArray 
	findIndices(IloNumArray binaryArray) {
		IloEnv env = binaryArray.getEnv();
		IloIntArray indices(env,IloSum(binaryArray));
		int i, l=0;
		for(i = 0; i < binaryArray.getSize(); i++){
			if(binaryArray[i]){
				indices[l] = i;
				l++;
			}
		}
		return indices;
}

//@method	f						:	To find the value of the function f := a*x + omega*norm(d*x)
IloNum 
	f(IloNumArray	x,
	  IloNumArray	a,
	  IloNumArray	d,
	  IloNum		omega) {
	
	IloNum	nCols	= a.getSize();
	int i;

	IloNum value = 0, varValue = 0;
	for (i = 0; i < nCols; i++)
		varValue += x[i]*d[i]*d[i];

	value = IloScalProd(a,x) + omega*sqrt(varValue);
	return value;
}

//@method	getComplement			:	To find the complement of a binary array
IloNumArray
	getComplement(IloNumArray binaryArray) {
		IloEnv env = binaryArray.getEnv();
		IloNumArray binaryArrayComp(env, binaryArray.getSize());
		
		for (int i = 0; i < binaryArray.getSize(); i++)
			binaryArrayComp[i] = 1 - binaryArray[i];

		return binaryArrayComp;
}

//@method	alreadyExists			:	To identify if a row already exists in a matrix.
bool
	alreadyExists(IloNumArray	pack,
				  IloNumArray2	packs) {
	
	bool isSame = false;
	int nRows = packs.getSize(), nCols;
	if (nRows > 0){
			nCols =  packs[0].getSize();
	}
	for (int i = 0; i < nRows; i++) {
		for (int j = 0; j < nCols; j++) {
			if (pack[j] == packs[i][j]) {
				isSame = true;
			}
			else {
				isSame = false;
				break;
			}
		}
		if(isSame){
			break;
		}
	}

	return isSame;
}

void 
	swap (int& x, 
		  int& y ) {
   int temp; 
   temp = x; 
   x = y; 
   y = temp; 
}

void 
	bubbleSort (IloNumArray Array, IloNumArray order) {
   IloInt size = Array.getSize();
   int last = size - 2; 
   int isChanged = 1;
   for(int i = 0; i < size; i++)
	   order[i] = i;
   while ( last >= 0 && isChanged) 
   { 
           isChanged = 0; 
           for ( int k = 0; k <= last; k++ ) 
			   if ( Array[k] > Array[k+1] ) 
               { 
				   swap ( Array[k], Array[k+1] );
                   swap ( order[k], order[k+1] );
				   isChanged = 1; 
               } 
           last--; 
   }
}


IloNumArray 
	getSubsets(IloNumArray	Array, 
					  IloNumArray	order, 
					  IloNum		limit,
					  IloNumArray	a,
					  IloNumArray	d,
					  IloNum		b,
					  IloNum		omega) {
	IloEnv env = Array.getEnv();
	IloNum nCols = Array.getSize();
	int i;
	IloNumArray pack(env, nCols);
	bool packFound = false;

	for(i = 0; i < nCols; i++) {
		pack[i] = 1;
	}

	IloNum	sum = 0;
	i = 0;
	while(i < nCols) {
		if (a[order[i]] == 0) {
			i++;
			continue;
		}
		pack[order[i]] = 0;
		sum += Array[order[i]];
		if(f(pack,a,d,omega) > b + EPS) {
			packFound = true;
			break;
		}
		else {
			i++;
		}
	}	
	if(packFound) {
		return pack;
	}
	else
		return IloNumArray(env, nCols);
}

//@method	getPacksUsingSort		:	To retrive a pack for the conic quadratic constraint using Greedy Algorithm.
void
	getPackUsingSort  (IloNumArray2	packs,
					  IloNumArray	a,
					  IloNumArray	d,
					  IloNum		b,
					  IloNum		omega,
					  IloNumArray	xbar) {
	int i, j, k,l;
	IloEnv	env		= xbar.getEnv();
	IloNum	nCols	= xbar.getSize();

	IloNumArray arrayToSort(env, nCols), order(env, nCols);

	IloNumArray	newPack(env,nCols);
	IloNumArray c(env, nCols);
	for (i = 0; i < nCols; i++) {
		c[i] = pow(omega*d[i],2);
	}
	IloNum	lambda, mu;	
	for (i = 0; i < nCols; i++) {
		if(a[i] == 0)
				continue;
		for (j = i + 1; j < nCols; j++) {
			if(a[j] == 0)
				continue;
			lambda	= (c[j]*xbar[i] - c[i]*xbar[j])/(c[j]*a[i] - c[i]*a[j]);
			mu		= (a[j]*xbar[i] - a[i]*xbar[j])/(c[i]*a[j] - c[j]*a[i]);
			if(lambda <= 0 && mu <= 0) {
				for (k = 0; k < nCols; k++) {
					arrayToSort[k] = xbar[k]/(lambda*a[k] + mu*c[k] + EPS);
				}
				bubbleSort(arrayToSort, order);
				newPack = getSubsets(xbar, order, 1, a, d, b, omega);
				if(IloSum(newPack) > 0 && !alreadyExists(newPack, packs)) {
					packs.add(newPack);
				}
			}
		}
	}
	arrayToSort.end(); order.end(); c.end();
}

//@method	makeMaximal					:	To make the pack maximal.
void
	makeMaximal(IloNumArray toExtend,
				IloNumArray	a,
				IloNumArray	d,
				IloNum		omega,
				IloNum		b) {
	int i;

	IloNum nCols	= a.getSize();
	IloNumArray fromExtend	= getComplement(toExtend);
	
	IloIntArray fromIndices = findIndices(fromExtend);
	
	for(i = 0; i < fromIndices.getSize(); i++) {
		if (a[fromIndices[i]] == 0) {
			toExtend[fromIndices[i]] = 1;
			continue;
		}
		toExtend[fromIndices[i]] = 1;
		if(f(toExtend, a , d, omega) <= b) {
			toExtend[fromIndices[i]] = 0;
		}
	}
}

IloNum 
	computeRho(IloNumArray	BinaryArray,
			   IloNum		indexplus,
			   IloNum		indexminus,
			   IloNumArray	a,
			   IloNumArray	d,
			   IloNum		omega) {
	int i, nCols = BinaryArray.getSize();
	IloEnv env = BinaryArray.getEnv();
	IloNumArray Array(env, nCols);

	for(i = 0; i < nCols; i++) {
		Array[i] = BinaryArray[i];
	}
	Array[indexminus] = 0;
	IloNum fval = f(Array, a, d, omega), fvalNew;
	Array[indexplus] = 1;
	fvalNew = f(Array, a, d, omega);
	IloNum rho = fvalNew - fval;

	return rho;
}

//@method	extendPack					:	To extend a pack inequality for the conic quadratic constraint.
IloNumArray
	extendPackIneq(IloNumArray	toExtend,
				   IloNumArray	a,
				   IloNumArray	d,
				   IloNum		omega,
				   IloNum		b) {

	int i, j, fromIndex;
	
	IloEnv env		= toExtend.getEnv();
	IloNum nCols	= a.getSize();

	IloNumArray fromExtend	= getComplement(toExtend);
	for (i = 0; i < nCols; i++) {
		if (a[i] == 0)
			fromExtend[i] = 0;
	}

	IloNum delta = f(fromExtend,a,d,omega) - b;

	IloIntArray	toIndices	= findIndices(toExtend);
	IloNumArray extendedPack(env, toExtend.getSize());
	
	for(i = 0; i < nCols; i++)
		extendedPack[i] = toExtend[i];

	IloIntArray fromIndices = findIndices(fromExtend);
	IloNum toSize = toIndices.getSize(), fromSize = fromIndices.getSize();
	IloNumArray toRhos(env, toSize);
	IloNum fromMin, toMin;

	for(i = 0; fromSize > 0 ; i++) {
		IloNumArray fromRhos(env,fromSize);

		for(i = 0; i < fromSize; i++) 
			fromRhos[i] = computeRho(fromExtend, fromIndices[i], fromIndices[i], a, d, omega);
		
		fromMin = IloMin(fromRhos);

		for(i = 0; i < fromSize; i++) {
			if(fromRhos[i] == fromMin) {
				fromIndex = i;
				break;
			}
		}
		
		for(i = 0; i < toSize; i++)
			toRhos[i] = computeRho(fromExtend, toIndices[i], fromIndices[fromIndex], a, d, omega);

		toMin = IloMin(toRhos);

		if (fromMin < toMin + delta) {
			extendedPack[fromIndices[fromIndex]] = 1;
			fromExtend[fromIndices[fromIndex]] = 0;
			fromIndices = findIndices(fromExtend);
			fromSize = fromIndices.getSize();
			delta = delta - IloMax(fromMin - toMin, 0);
		}
		else
			break;

		fromRhos.end();
		}
	return extendedPack;
}


IloNumArray
	findGradient(IloNumArray	X,
				 IloNumArray	minCut,
				 IloNum&		rhs,
				 IloNum			b,
				 IloNum			nbArcs,
				 IloNum			nbNodes,
				 IloNumArray	a,
				 IloNumArray	d,
				 IloNum			omega,
				 IloNumArray2	N) {
	IloEnv env = N.getEnv();
	int i,j;
	/* Finding the point to take gradient */
	IloNumVarArray pointvar(env,nbArcs,0,1);
	IloNumVar tempvar(env, 0, IloInfinity);
	IloNumArray point(env, nbArcs);
	IloNumArray gradient(env,nbArcs);
	IloNum functionVal = 0;
	IloNumExprArray obj(env, nbArcs);
	for(i = 0; i < nbArcs; i++) {
		obj[i] = X[i] - pointvar[i];
	}

	IloModel modelFindPoint(env);
	modelFindPoint.add(IloMinimize(env,IloScalProd(obj,obj)));
	IloExpr consMeanTerm(env);
	IloExpr consVarTerm(env);
	for(i = 0; i < nbArcs; i++) {
		consMeanTerm += a[i]*minCut[i]*pointvar[i];
		consVarTerm += pow(d[i],2)*minCut[i]*pointvar[i]*pointvar[i];
		modelFindPoint.add(pointvar[i] >= 0);
	}
	modelFindPoint.add(tempvar == consMeanTerm - b);
	modelFindPoint.add(tempvar*tempvar >= omega*omega*consVarTerm);
	IloCplex cplexPoint(modelFindPoint);
	cplexPoint.setParam(IloCplex::BarQCPEpComp, 1e-10);
	cplexPoint.setOut(env.getNullStream());
	cplexPoint.setWarning(env.getNullStream());
	cplexPoint.solve();
	
	cplexPoint.getValues(point, pointvar);

	IloNum mean = cplexPoint.getValue(consMeanTerm), var = cplexPoint.getValue(consVarTerm);
			  
	functionVal = mean - omega*sqrt(var) - b;

	for(i = 0; i < nbArcs; i++)
		gradient[i] = a[i]*minCut[i] - (1/sqrt(var))*omega*pow(d[i],2)*minCut[i]*point[i];

	rhs = IloScalProd(point,gradient) - functionVal;

	point.end(); pointvar.end(); tempvar.end(); obj.end(); modelFindPoint.end(); cplexPoint.end();
	consMeanTerm.end(); consVarTerm.end();

	return gradient;
}

IloNumArray 
	findMinimumCut(IloNumArray	X,
				   IloNum&		sepObj,
				   IloNum		nbArcs,
				   IloNum		nbNodes,
				   IloNumArray2	N,
				   IloNumArray	a,
				   IloNumArray	d,
				   IloNum		omega) {
	/*-------------------------------Separation Problem ----------------------------------*/
	IloEnv env = N.getEnv();
	IloNumArray capacitySubMean(env,nbArcs), capacitySubVariance(env,nbArcs);
	IloNumArray minimumCut(env, nbArcs);
	
	int i, j;
	/* Modeling the Separation Problem */
	
	for(i = 0; i < nbArcs; i++) {
		capacitySubMean[i] = a[i]*X[i];
		capacitySubVariance[i] = pow(d[i],2)*X[i]*X[i];
	}
	
	IloModel modelSeparation(env);
	IloNumVarArray lambda(env, nbNodes, 0, IloInfinity);
	IloIntVarArray minCut(env, nbArcs, 0, 1);
	IloNumVar t(env, -IloInfinity, IloInfinity);
	
	/* Adding the constraints */
	modelSeparation.add(lambda[0] == 1);
	modelSeparation.add(lambda[nbNodes-1] == 0);
	for(i = 0; i < nbArcs; i++) {
		modelSeparation.add(lambda[N[i][1]-1] - lambda[N[i][2]-1] <= minCut[N[i][0]-1]);
		modelSeparation.add(lambda[N[i][1]-1] + lambda[N[i][2]-1] >= minCut[N[i][0]-1]);
			  modelSeparation.add(lambda[N[i][1]-1] + lambda[N[i][2]-1] <= 2 - minCut[N[i][0]-1]);
			  modelSeparation.add(lambda[N[i][1]-1] - lambda[N[i][2]-1] >= minCut[N[i][0]-1] - 1);
		  }

		  modelSeparation.add(lambda);
		  modelSeparation.add(minCut);
		  modelSeparation.add(t*t <= pow(omega,2)*IloScalProd(capacitySubVariance,minCut));
		  
		  /* Adding the objective */
		  IloExpr objseparation = IloScalProd(capacitySubMean, minCut) - t;
		  modelSeparation.add(IloMinimize(env, objseparation));
		  objseparation.end();
		  
		  /* Solving the separation problem */
		  IloCplex cplexSeparation(modelSeparation);
		  cplexSeparation.setOut(env.getNullStream());
		  cplexSeparation.setWarning(env.getNullStream());
		  
		  cplexSeparation.solve();
		  
		  sepObj = cplexSeparation.getObjValue();
		  cplexSeparation.getValues(minimumCut, minCut);
		  capacitySubMean.end(); capacitySubVariance.end();
		  modelSeparation.end(); cplexSeparation.end();
		  lambda.end(); minCut.end(); t.end();
		  /*-------------------Separation Problem Ends Here--------------------*/
		  return minimumCut;
}


bool 
	validateConic(IloNumArray		X, 
				  IloNum			b, 
				  IloModel			model,
				  IloNum			nbArcs,
				  IloNum			nbNodes,
				  IloNumVarArray	x,
				  IloNumArray		a,
				  IloNumArray		d,
				  IloNumVar			temp,
				  IloNum			omega,
				  IloNumArray2		N,
				  IloNum&			sepObj) {	
	
	IloEnv env = model.getEnv();
	bool flag = false;
	IloNumArray minimumCut = findMinimumCut(X, sepObj,nbArcs, nbNodes, N, a, d, omega);
	/*--------Testing the optimality and generating the conic cut for the relaxation problem--------*/
	if(sepObj < b) {
		/* Setting the flag for optimality */
		flag = false;
		int i;
		IloExpr a_expr(env);
		IloExpr d_expr(env);
			
		for (i = 0; i < nbArcs; i++) {
			a_expr += x[i] * a[i] * minimumCut[i];
			d_expr += x[i] * x[i] * pow(d[i],2) * minimumCut[i]; 
		}
		
		model.add(a_expr - b >= temp);
		model.add(pow(omega,2) * d_expr <= temp*temp);
		cutsAdded++;
		a_expr.end();
		d_expr.end(); 
	}
	else
		flag = true;

	return flag;
}

ILOUSERCUTCALLBACK7(userextendedPackInequalities,
					IloNumVarArray,		x,
					const IloNumArray2, N,
					const IloNumArray,	a,
					const IloNumArray,	d, 
					const IloNum,		omega,
					const IloNum,		b,
					const IloInt,		nbNodes) {
	//if (getNnodes() == 0) {
      try {
		   int i;
		   IloEnv env		=	getEnv();
		   IloInt nbArcs	=	a.getSize();
		   IloNumArray	X(env, nbArcs);
		   IloNumArray2	packs(env);
		   IloNumArray currentPack(env, nbArcs), packComplement(env, nbArcs), extended(env, nbArcs);
		   IloNum rhs;
		   getValues(X,x);
		   

		   IloNumArray a_pack(env, nbArcs), d_pack(env,nbArcs);
		   IloNum b_pack;
		   
		   IloNumArray minCut = findMinimumCut(X, sepObjValue, nbArcs, nbNodes, N, a, d, omega);
		   
		   if(sepObjValue < b) {
			   for(i = 0; i < nbArcs; i++) {
				   a_pack[i] = -a[i]*minCut[i];
				   d_pack[i] = d[i]*minCut[i];
			   }
			   b_pack = -b;
			   getPackUsingSort(packs, a_pack, d_pack, b_pack, omega, X);
			   for (i = 0; i < packs.getSize(); i++) {
				   currentPack = packs[i];
				   makeMaximal(currentPack, a_pack, d_pack, omega, b_pack);
				   packComplement	= getComplement(currentPack);
				   rhs				= IloSum(packComplement);
				   extended			= extendPackIneq(packComplement, a_pack, d_pack, omega, b_pack);
				   rhs				= IloSum(extended) - rhs + 1;
				   
				   if(IloScalProd(extended,X) < rhs - EPSILON) {
					   IloRange	cut;
					   try {
						   cut = (IloScalProd(extended,x) >= rhs);
						   //cout << cut << endl << endl;
						   add(cut).end();
					   }
				   
					   catch(...) {
						   cut.end();
						   throw;
					   }
				   }
			   }
			   packs.end(); currentPack.end(); packComplement.end();
			   extended.end(); minCut.end(); X.end(); a_pack.end(); d_pack.end();
		   }
	   }
	   catch (IloException &e) {
		   cerr << "Error in extendedPackInequalities Callback: " << e << endl;
		   throw;
		   }
//	}
 }

ILOLAZYCONSTRAINTCALLBACK7(lazyextendedPackInequalities,
					IloNumVarArray,		x,
					const IloNumArray2, N,
					const IloNumArray,	a,
					const IloNumArray,	d, 
					const IloNum,		omega,
					const IloNum,		b,
					const IloInt,		nbNodes) {
		  try {
			   int i;
			   IloEnv env		=	getEnv();
			   IloInt nbArcs	=	a.getSize();
			   IloNumArray	X(env, nbArcs);
			   IloNumArray2	packs(env);
			   IloNumArray currentPack(env, nbArcs), packComplement(env, nbArcs), extended(env, nbArcs);
			   IloNum rhs;
			   getValues(X,x);
			   for (i = 0; i < nbArcs ; i++)
				   X[i] = IloRound(X[i]);
			   
			   IloNumArray a_pack(env, nbArcs), d_pack(env,nbArcs);
			   IloNum b_pack;
		   
			   IloNumArray minCut = findMinimumCut(X, sepObjValue, nbArcs, nbNodes, N, a, d, omega);
		   
			   if(sepObjValue < b) {
				   for(i = 0; i < nbArcs; i++) {
					   a_pack[i] = -a[i]*minCut[i];
					   d_pack[i] = d[i]*minCut[i];
				   }
				   b_pack = -b;
				   getPackUsingSort(packs, a_pack, d_pack, b_pack, omega, X);
				   for (i = 0; i < packs.getSize(); i++) {
					   currentPack = packs[i];
					   makeMaximal(currentPack, a_pack, d_pack, omega, b_pack);
					   packComplement	= getComplement(currentPack);
					   rhs				= IloSum(packComplement);
					   extended			= extendPackIneq(packComplement, a_pack, d_pack, omega, b_pack);
					   rhs				= IloSum(extended) - rhs + 1;
				   
					   if(IloScalProd(extended,X) < rhs - EPSILON) {
						   IloRange	cut;
						   try {
							   cut = (IloScalProd(extended,x) >= rhs);
							   add(cut).end();
						   }
				   
						   catch(...) {
							   cut.end();
							   throw;
						   }
					   }
				   }
				   packs.end(); currentPack.end(); packComplement.end();
				   extended.end(); minCut.end(); X.end(); a_pack.end(); d_pack.end();
			   }
		   }
		   catch (IloException &e) {
			   cerr << "Error in extendedPackInequalities Callback: " << e << endl;
			   throw;
		   }
 }

ILOLAZYCONSTRAINTCALLBACK7(lazylinearizedInequalities,
					IloNumVarArray,		x,
					const IloNumArray2, N,
					const IloNumArray,	a,
					const IloNumArray,	d, 
					const IloNum,		omega,
					const IloNum,		b,
					const IloInt,		nbNodes) {
      try {
		   IloEnv env		=	getEnv();
		   IloInt nbArcs	=	a.getSize();
		   IloNumArray	X(env, nbArcs), gradient(env,nbArcs);
		   int i;
		   getValues(X,x);
		   
		   for (i = 0; i < nbArcs ; i++)
			   X[i] = IloRound(X[i]);
		   
		   IloNumArray minCut = findMinimumCut(X, sepObjValue, nbArcs, nbNodes, N, a, d, omega);
		   if(sepObjValue < b) {
			   IloNum rhs;
			   gradient = findGradient(X,minCut,rhs,b,nbArcs,nbNodes,a,d,omega,N);
			   IloRange	cut;
			   try {
				   cut = (IloScalProd(gradient,x) >= rhs);
				   add(cut).end();
			   }
			   catch(...) {
				   cut.end();
				   throw;
			   }
		   }
	   }
	   catch (IloException &e) {
		   cerr << "Error in linearizedInequalities Callback: " << e << endl;
		   throw;
	   }
}

ILOUSERCUTCALLBACK7(userlinearizedInequalities,
					IloNumVarArray,		x,
					const IloNumArray2, N,
					const IloNumArray,	a,
					const IloNumArray,	d, 
					const IloNum,		omega,
					const IloNum,		b,
					const IloInt,		nbNodes) {
      try {
		   IloEnv env		=	getEnv();
		   IloInt nbArcs	=	a.getSize();
		   IloNumArray	X(env, nbArcs), gradient(env,nbArcs);
		   int i;
		   getValues(X,x);
		   
		   IloNumArray minCut = findMinimumCut(X, sepObjValue, nbArcs, nbNodes, N, a, d, omega);
		   if(sepObjValue < b) {
			   IloNum rhs;
			   gradient = findGradient(X,minCut,rhs,b,nbArcs,nbNodes,a,d,omega,N);
			   IloRange	cut;
			   try {
				   cut = (IloScalProd(gradient,x) >= rhs);
				   add(cut).end();
			   }
			   catch(...) {
				   cut.end();
				   throw;
			   }
		   }
	   }
	   catch (IloException &e) {
		   cerr << "Error in linearizedInequalities Callback: " << e << endl;
		   throw;
	   }
}

//@method	buildCplexModel				:	To build the CPLEX Model from given parameters.
void
	buildCplexModel(IloModel			model,
					IloNumVarArray		x,
					IloNumVarArray		y,
					const IloNumArray2  N,
					const IloNumArray	a,
					const IloNumArray	d,
					const IloNum		b,
					const IloNum		omega,
					const IloNumArray	c,
					const IloInt		nbNodes,
					const IloInt		nbArcs) {

	int i, j, k, l;
	IloEnv env = model.getEnv();
	x.clear();
	y.clear();

	IloNumVarArray tmp1(env, nbArcs, 0, 1, ILOINT);
	IloNumVarArray tmp2(env, nbArcs, 0, 1, ILOFLOAT);
	x.add(tmp1);
	y.add(tmp2);
	tmp1.end();
	tmp2.end();
	
	model.add(IloMinimize(env, IloScalProd(c,x)));
	
	model.add(x);
	model.add(y);

	for(i = 1; i <= nbNodes; i++) {
		  IloExpr v(env);
		  for(j = 0; j < nbArcs; j++) {
			  if(N[j][1] == i) {
				  l = N[j][0]-1;
				  v += y[l]*a[l];
			  }
			  else if(N[j][2] == i) {
				  l = N[j][0]-1;
				  v -= y[l]*a[l];
			  }
		  }
		  if(i ==  1)
			  model.add(v == b);
		  else if(i == nbNodes)
			  model.add(v == -b);
		  else
			  model.add(v == 0);
		  v.end();
	  }

	  for(i = 0; i < nbArcs; i++) {
		  /* Following constraints to imply isChosen == ceil(flow/capacityMean) */
		  model.add(y[i] <= x[i]);
		  //model.add(y[i]/a[i] >= x[i] - 1 + EPSILON);
	  }
}


int
	main(int argc, char **argv) {
	static IloEnv env;
	try {
		  static IloInt i, j, k, l;
		  static IloInt totalNodes = 0;
		  static IloInt nbNodes;
		  static IloInt nbArcs;
		  static IloInt incidenceSize;
		  static bool flag = false;
		  static IloNum omega;
		  static IloNum b, beta;
		  static IloNumArray a(env), d(env), c(env);
		  static IloNumArray2 N(env);
		  static ofstream fout;
		  
		  int algo = 0;
		  
		  time_t start, end;
		  
		  double gap, cpuTime = 0, objValue;
		  
		  char input[100]	= "../Data/";
		  char output[100]	= "../ComputationSummary/";
		  const char* input_file = strcat(strcat(input,argv[1]),".dat");
		  
		  const char* filename  = input_file;
		  
		  for (i = 2; i < argc-1; i++) { //command line options
			  if (!strncmp(argv[i],  "-a", 2)) {
				  algo = atoi(argv[++i]); //The type of user cuts to use, 0: No Cuts, 1: Linearized, 2: Packs 
			  }
		  }

		  ifstream file(filename);
		  if (!file) {
			 cerr << "ERROR: could not open file '" << filename
				  << "' for reading" << endl;
			 usage(argv[0]);
			 exit(1);
			 throw(-1);
		  }
		  
		  file >> omega >> beta >> c >> a >> d >> N;

		  nbArcs = N.getSize();
		  
		  IloNumArray temp(env, nbArcs);
		  
		  for(i = 0; i < nbArcs; i++)
			  temp[i] = N[i][2];
		  
		  nbNodes = IloMax(temp);
		  temp.end();

		  // Determining 'b = \beta * mincut'

		  {
			  IloNumArray all(env, nbArcs);
			  for (i = 0; i < nbArcs; i++) {
				  all[i] = 1;
			  }

			  findMinimumCut(all, b, nbArcs, nbNodes, N, a, d, omega);

			  b = beta * b;
		  }

		  IloNumArray sol(env, nbArcs);

		  // Build CPLEX model

		  IloModel			model(env);
		  IloNumVarArray	x(env);
		  IloNumVarArray	y(env);
		  buildCplexModel(model, x, y, N, a, d, b, 
										omega, c, nbNodes, nbArcs);

		  // Solve CPLEX standard model

		  IloCplex cplex(env);
		  cplex.setOut(env.getNullStream());
		  cplex.setWarning(env.getNullStream());
		  
		  //cplex.exportModel("myModel.lp");
		  
		  // Setting the CPLEX Parameters

		  cplex.setParam(IloCplex::HeurFreq, -1);
		  cplex.setParam(IloCplex::MIQCPStrat, 1);
		  cplex.setParam(IloCplex::TiLim, TIM_LIM);
		  cplex.setParam(IloCplex::TreLim, 100);
		  cplex.setParam(IloCplex::MIPSearch, IloCplex::Traditional);
		  cplex.setParam(IloCplex::Threads, 1);
		  
		  /*
		  cplex.setParam(IloCplex::MIPInterval, 1000);
		  cplex.setParam(IloCplex::EpGap, 1e-09);
		  cplex.setParam(IloCplex::PolishAfterEpGap, 1e-09);
		  cplex.setParam(IloCplex::BarEpComp, 1e-12);
		  cplex.setParam(IloCplex::BarQCPEpComp, 1e-12);
		  cplex.setParam(IloCplex::MIPDisplay, 2);
		  cplex.setParam(IloCplex::MIPInterval, 1);
		  cplex.setParam(IloCplex::BarDisplay, 1);
		  cplex.setParam(IloCplex::FlowCovers, -1);
		  cplex.setParam(IloCplex::GUBCovers, -1);
		  cplex.setParam(IloCplex::FracCuts, -1);
		  cplex.setParam(IloCplex::FlowPaths, -1);
		  cplex.setParam(IloCplex::DisjCuts, -1);
		  cplex.setParam(IloCplex::Covers, -1);
		  cplex.setParam(IloCplex::Cliques, -1);
		  cplex.setParam(IloCplex::ImplBd, -1);
		  cplex.setParam(IloCplex::MCFCuts, -1);
		  cplex.setParam(IloCplex::MIRCuts, -1);
		  cplex.setParam(IloCplex::ZeroHalfCuts, -1);
		  cplex.setParam(IloCplex::EachCutLim, 0);
		  cplex.setParam(IloCplex::CutPass, -1);
		  cplex.setParam(IloCplex::TuningDisplay, 3);
		  cplex.setParam(IloCplex::MPSLongNum, 0);
		  */		  
		  
		  if (algo == 0) {
			  /* Starting the iterative procedure */
			  while(flag == 0 && cpuTime <= TIM_LIM) {
				  cplex.clearModel();
				  cplex.extract(model);
				  // Optimize the problem and obtain solution.
				  cplex.setParam(IloCplex::TiLim, TIM_LIM - cpuTime);
				  start = clock();
				  cplex.solve();
				  cplex.getValues(sol, x);
				  objValue	= cplex.getObjValue();
				  totalNodes += cplex.getNnodes();
				  /* For linear use this */
				  for (i = 0; i < nbArcs ; i++)
					  sol[i] = IloRound(sol[i]);
		  
				  /*-------------------Relaxation Problem Ends Here--------------------*/
				  IloNumVar newvar(env, 0, IloInfinity, ILOFLOAT);
				  flag = validateConic(sol,b,model,nbArcs,nbNodes,x,a,d,newvar,omega,N,sepObjValue);
				  end = clock();
				  cpuTime	+= (double)(end - start) / CLOCKS_PER_SEC;
			  }
		  }
		  
		  if (algo == 1) {
			  cplex.clearModel();
			  cplex.extract(model);
			  cplex.use(lazylinearizedInequalities(env,x,N,a,d,omega,b,nbNodes));
			  cplex.use(userlinearizedInequalities(env,x,N,a,d,omega,b,nbNodes));
			  start = clock();
			  cplex.solve();
			  end	= clock();
			  objValue	= cplex.getObjValue();
			  totalNodes = cplex.getNnodes();
			  cutsAdded = cplex.getNcuts(IloCplex::CutUser);
			  cpuTime	= (double)(end - start) / CLOCKS_PER_SEC;
			  if (cplex.getStatus() == IloAlgorithm::Optimal)
				  flag = true;
			  else
				  flag = false;
		  }
			
		  if (algo == 2) {
			  cplex.clearModel();
			  cplex.extract(model);
			  cplex.use(lazyextendedPackInequalities(env,x,N,a,d,omega,b,nbNodes));
			  cplex.use(userextendedPackInequalities(env,x,N,a,d,omega,b,nbNodes));
			  start = clock();
			  cplex.solve();
			  end	= clock();
			  objValue	= cplex.getObjValue();
			  totalNodes = cplex.getNnodes();
			  cutsAdded = cplex.getNcuts(IloCplex::CutUser);
			  cpuTime	= (double)(end - start) / CLOCKS_PER_SEC;
			  if (cplex.getStatus() == IloAlgorithm::Optimal)
				  flag = true;
			  else
				  flag = false;
		  }	

		  if(cpuTime < 0)
			  cpuTime	= (double)(end - start) / CLOCKS_PER_SEC;
		  
		  const char* output_file;

		  if (algo == 0) 
			  output_file = strcat(strcat(output,"ConicConstraints"),".log");
		  else if (algo == 1)
			  output_file = strcat(strcat(output,"LinearizedCuts"),".log");
		  else if (algo == 2)
			  output_file = strcat(strcat(output,"ExtendedPacksCuts"),".log");


		  if(FileExists(output_file)) {
			  fout.open(output_file, ios::app);
			  fout << nbNodes << "\t";
			  fout << nbArcs << "\t";
			  fout << beta << "\t";
			  fout << omega << "\t";
			  if (flag)
				  fout << "OPTIMAL \t" ;
			  else
				  fout << "NOT OPTIMAL \t";

			  fout << objValue << "\t";
			  fout << cutsAdded << "\t";
			  fout << totalNodes << "\t" ;
			  fout << cpuTime << "\n";
		  }

		  else {
			  fout.open(output_file);
			  fout << "NODES\t";
			  fout << "ARCS\t";
			  fout << "BETA\t";
			  fout << "OMEGA\t";
			  fout << "STATUS\t";
			  fout << "OBJ VAL\t";
			  fout << "# CUTS\t";
			  fout << "# NODES\t";
			  fout << "CPUTIME\n";
			  fout << nbNodes << "\t";
			  fout << nbArcs << "\t";
			  fout << beta << "\t";
			  fout << omega << "\t";
			  if (flag)
				  fout << "OPTIMAL \t" ;
			  else
				  fout << "NOT OPTIMAL \t";

			  fout << objValue << "\t";
			  fout << cutsAdded << "\t";
			  fout << totalNodes << "\t" ;
			  fout << cpuTime << "\n";
		  }
		  cplex.end();
		  fout.close();
	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}

	env.end();
	return 0;
}  // END main