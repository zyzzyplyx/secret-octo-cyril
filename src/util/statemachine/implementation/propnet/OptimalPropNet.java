package util.statemachine.implementation.propnet;

import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;

import util.gdl.grammar.Gdl;
import util.gdl.grammar.GdlConstant;
import util.gdl.grammar.GdlProposition;
import util.gdl.grammar.GdlRelation;
import util.gdl.grammar.GdlSentence;
import util.gdl.grammar.GdlTerm;
import util.propnet.architecture.Component;
import util.propnet.architecture.PropCode;
import util.propnet.architecture.PropNet;
import util.propnet.architecture.propClassLoader;
import util.propnet.architecture.components.Or;
import util.propnet.architecture.components.Proposition;
import util.propnet.architecture.components.Transition;
import util.propnet.factory.OptimizingPropNetFactory;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.propnet.SamplePropNetStateMachine.AuxNode;
import util.statemachine.implementation.prover.query.ProverQueryBuilder;
import util.statemachine.implementation.prover.result.ProverResultParser;

public class OptimalPropNet extends StateMachine {
    /** The underlying proposition network  */
    private PropNet propNet;
    /** The topological ordering of the propositions */
    private List<Component> ordering;
    /** The player roles */
    private List<Role> roles;
    /**The factors of this game, with their goal states as keys*/
    Map<Component, Set<Component>> factors;
    Map<Component, Set<Integer>> factorLegalsMap;
    LinkedList<Component> goalOrdering;
    
    private MachineState initialState;
    private MachineState currentState;
    private PropCode propCode;
    private boolean[] boolState;
    //private int heurs;
    private Map<Integer, GdlSentence> transMap;
    private Map<Integer, Double> heuristicMap;
    private Map<Role, Map<Integer, Move>> moveMap;
    
	Set<Proposition> latches = new HashSet<Proposition>();
	Set<Proposition> falseLatches = new HashSet<Proposition>();
    
    /**
     * Initializes the PropNetStateMachine. You should compute the topological
     * ordering here. Additionally you may compute the initial state here, at
     * your discretion.
     */
    @Override
    public StateMachine initialize(List<Gdl> description) {
        try {
			propNet = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
        roles = propNet.getRoles();
        ordering = getOrdering();
        if(ordering == null){
        	System.out.println("bailing out");
        	StateMachine sample = new SamplePropNetStateMachine();
        	sample.initialize(description);
        	return sample;
        }
        moveMap = makeMoveMap();
        initialState = computeInitialState();
        //propNet.renderToFile("graph.dot");
        //System.out.println("order: "+ordering.toString());
        System.out.println("initState: "+initialState.toString());
        return this;
    }    
    
    private Map<Role, Map<Integer, Move>> makeMoveMap(){
    	Map<Role, Map<Integer, Move>> mm = new HashMap<Role, Map<Integer, Move>>();
    	for(Role r : propNet.getRoles()){
    		Map<Integer, Move> indMap = new HashMap<Integer, Move>();
    		Set<Proposition> legalProp = propNet.getLegalPropositions().get(r);
			for(Proposition prop : legalProp){	
				indMap.put(prop.bitIndex, getMoveFromProposition(prop));
			}
			mm.put(r, indMap);
    	}
    	return mm;
    }
    
    private MachineState computeInitialState()
	{
    	clearPropNet();
    	boolState[propNet.getInitProposition().bitIndex] = true;
    	return updateStateMachine(new MachineState(new HashSet<GdlSentence>()));//empty base
	}
    
	/**
	 * Computes if the state is terminal. Should return the value
	 * of the terminal proposition for the state.
	 */
    @Override
    public boolean isTerminal(MachineState state) {
		if(!state.equals(currentState)){
			clearPropNet();
			updateStateMachine(state);
		}
		//once the state machine is on the right state, it's easy to read get terminal
        return boolState[propNet.getTerminalProposition().bitIndex];
    }
	
	/**
	 * Computes the goal for a role in the current state.
	 * Should return the value of the goal proposition that
	 * is true for that role. If there is not exactly one goal
	 * proposition true for that role, then you should throw a
	 * GoalDefinitionException because the goal is ill-defined. 
	 */
    @Override
    public int getGoal(MachineState state, Role role)
    throws GoalDefinitionException {
		if(!state.equals(currentState)){
			clearPropNet();
			updateStateMachine(state);
		}
        Set<Proposition> goals = propNet.getGoalPropositions().get(role);
        Proposition goal = null;
        //loop over goals and make sure only one is true in this state
        for(Proposition g : goals){
            if(boolState[g.bitIndex]){
                if(goal != null) throw new GoalDefinitionException(state, role);
                goal = g;
            }
        }
        if(goal == null) throw new GoalDefinitionException(state, role);
        return getGoalValue(goal);
    }
	
	/**
	 * Returns the initial state. The initial state can be computed
	 * by only setting the truth value of the INIT proposition to true,
	 * and then computing the resulting state.
	 */
	@Override
	public MachineState getInitialState() {
		return initialState;
	}
	
	
	public Map<Component, Set<Component>> getFactorMap(){
		return factors;
	}
	
	public List<Move> getFactorLegalMoves(MachineState state, Role role, Component factorKey){
		if(!state.equals(currentState)){
			clearPropNet();
			updateStateMachine(state);
		}
		Set<Integer> factorLegals = factorLegalsMap.get(factorKey);
		//just check propositions corresponding to all possible moves for role
		//move is legal if the proposition is true
		List<Move> moves = new ArrayList<Move>();
		Map<Integer, Move> moveInd = moveMap.get(role);
		for(int i : moveInd.keySet()){	
			if(boolState[i] && factorLegals.contains(i)) moves.add(moveInd.get(i));
		}
		/*
		if(moves.size() == 0){
			for(Proposition prop : legalProp){
				System.out.println("prop: "+prop.toString());
				System.out.println("val: "+prop.getValue());
				System.out.println("contained: "+selectedLegals.contains(prop));
			}
		}
		*/
		return moves;
	}
	
	/**
	 * Computes the legal moves for role in state, returning a set which only affects a single
	 * factor.  It prefers to return moves affecting the primary goal game, but if there are no 
	 * moves in that game it chooses another.
	 */
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role)
	throws MoveDefinitionException {
		List<Move> moves = new ArrayList<Move>();
		if(goalOrdering == null){
			if(!state.equals(currentState)){
				clearPropNet();
				updateStateMachine(state);
			}
			Map<Integer, Move> moveInd = moveMap.get(role);
			for(int i : moveInd.keySet()){	
				if(boolState[i]) moves.add(moveInd.get(i));
			}
			return moves;
		}
		else{
			for(Component factorKey : goalOrdering){
				moves = getFactorLegalMoves(state, role, factorKey);
				if(moves.size() > 0) return moves;
			}
		}
		return moves;
	}
	
	/**
	 * Fetches the heuristic value generated the last time the statemachine was fed a new state.
	 */
	@Override
	public double getHeuristic(MachineState state){
		double heurs = 0;
		if(!state.equals(currentState)){
			clearPropNet();
			updateStateMachine(state);
		}
		for(int i : heuristicMap.keySet()){
			heurs += (boolState[i]? heuristicMap.get(i):0);
		}
		return heurs;
	}
	
	/**
	 * Computes the next state given state and the list of moves.
	 */
	@Override
	public MachineState getNextState(MachineState state, List<Move> moves)
	throws TransitionDefinitionException {
		clearPropNet();
    	//Use the moves to define inputs for the next state
		Map<GdlTerm, Proposition> termToProps = propNet.getInputPropositions();
		List<GdlTerm> moveTerms = toDoes(moves);
		for (GdlTerm m : moveTerms) {
			boolState[termToProps.get(m).bitIndex] = true;
		}
		return updateStateMachine(state);
	}
	
	private void clearPropNet(){
		boolState = new boolean[propNet.getComponents().size()];
	}
    
    private MachineState updateStateMachine(MachineState state) {
    	//System.out.println("------------------------------------------------------------------------------------------");
		//map the state to base propositions
		Map<GdlTerm, Proposition> bases = propNet.getBasePropositions();
		for (GdlSentence s : state.getContents()) {
			boolState[bases.get(s.toTerm()).bitIndex] = true;
		}
		boolState = propCode.setPropNet(boolState);
    	currentState = state;
    	return getStateFromBase();
    }    
	
	/**
	 * This should compute the topological ordering of propositions.
	 * Each component is either a proposition, logical gate, or transition.
	 * Logical gates and transitions only have propositions as inputs.
	 * 
	 * The base propositions and input propositions should always be exempt
	 * from this ordering.
	 * 
	 * The base propositions values are set from the MachineState that
	 * operations are performed on and the input propositions are set from
	 * the Moves that operations are performed on as well (if any).
	 * 
	 * @return The order in which the truth values of propositions need to be set.
	 */
	public List<Component> getOrdering()
	{
		  try {
		   FileOutputStream fout = new FileOutputStream("src/boolCode/boolPropNet.java");
		   fout.write(("package boolCode;" +
		   				"public class boolPropNet implements util.propnet.architecture.PropCode {\n\n" +
				   		"public boolPropNet(){}\n\n"+
		                "public boolean[] setPropNet(boolean[] b){\n").getBytes());
		  // List to contain the topological ordering.
	       List<Component> order = new LinkedList<Component>();
	       List<Proposition> orderFinal = new LinkedList<Proposition>();
	       
	       Set<Component> solved = new HashSet<Component>();
	       solved.add(propNet.getInitProposition());
	       solved.addAll(propNet.getBasePropositions().values());
	       solved.addAll(propNet.getInputPropositions().values());
	       int numToSolve = propNet.getPropositions().size() - solved.size() + propNet.getBasePropositions().size();// +propNet.getInputPropositions().size();//all propositions and transitions
	       
	       int bitCounter = 0;
	       int byteCounter = 0;
	       int methodCounter = 0;
	       for(Component c : solved){
	    	   c.bitIndex = bitCounter;
	    	   bitCounter++;
	       }
	       Set<Component> nowSolved = new HashSet<Component>();
	       while(order.size() < numToSolve){
	    	   nowSolved = new HashSet<Component>();
	           for(Component comp : propNet.getComponents()){	   
	        	   if(!solved.contains(comp)){
	            	   boolean allSolved = true;
	                   for(Component in : comp.getInputs()){
	                	   if(!solved.contains(in)){
	                		   allSolved = false;
	                		   break;
	                	   }
	                   }
	                   if(allSolved){
	                	   nowSolved.add(comp);
	                	   if((comp instanceof Proposition)||(comp instanceof Transition)){
	                		   comp.bitIndex = comp.getSingleInput().bitIndex;
	                		   order.add(comp);
                		   }
                		   else{
                			   comp.bitIndex = bitCounter;
		                	   bitCounter++;
		                	   byteCounter += comp.getInputs().size() * 16;
		                	   if(byteCounter > 15000){
		                		   methodCounter++;
		                		   if(methodCounter > 250) return null;
		                		   byteCounter = comp.getInputs().size() * 16;
		                		   fout.write(("\n b=set"+bitCounter+"(b);"+
		                				   	  "return b;\n}\n"+
		                				   	  "private boolean[] set"+bitCounter+"(boolean[] b){\n").getBytes());
		                	   }
		                	   fout.write((comp.getEvalExp()).getBytes());
	                	   }
	                   }
	               }
	           }
	           solved.addAll(nowSolved);
	       }
	        
	       System.out.println("\n---------------------\n\n"+propNet.getComponents().size()+"\n------------------------\n");
	       
	       //-----------------COMPILATION-------------------//
	       fout.write(("return b;\n}\n}").getBytes());
		   fout.close();
            JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
            int compilationResult = compiler.run(null, null, null, "src/boolCode/boolPropNet.java");
            if(compilationResult == 0){
                System.out.println("Compilation is successful");
            }else{
                System.out.println("Compilation Failed");
            }
            
            try
            {    
                // Create a new class loader with the directory
                ClassLoader loader = new propClassLoader(propClassLoader.class.getClassLoader());
                Class propClass = loader.loadClass("boolPropNet");
                propCode = (PropCode) propClass.newInstance();
            }
            catch (ClassNotFoundException e)
            { 
            	e.printStackTrace();
            }
            catch (Exception ex)
            {
                ex.printStackTrace();
            }
            //------------------END COMPILATION---------------//
            transMap = new HashMap<Integer, GdlSentence>();
            for(Proposition p : propNet.getBasePropositions().values()){
            	transMap.put(p.getSingleInput().bitIndex, p.getName().toSentence());
            }
            
            
	        return order;
		    
		    } catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}       
		  return null;
	}
	
	/* Already implemented for you */
	@Override
	public List<Role> getRoles() {
		return roles;
	}

	/* Helper methods */
		
	/**
	 * The Input propositions are indexed by (does ?player ?action).
	 * 
	 * This translates a list of Moves (backed by a sentence that is simply ?action)
	 * into GdlTerms that can be used to get Propositions from inputPropositions.
	 * and accordingly set their values etc.  This is a naive implementation when coupled with 
	 * setting input values, feel free to change this for a more efficient implementation.
	 * 
	 * @param moves
	 * @return
	 */
	private List<GdlTerm> toDoes(List<Move> moves)
	{
		List<GdlTerm> doeses = new ArrayList<GdlTerm>(moves.size());
		Map<Role, Integer> roleIndices = getRoleIndices();
		
		for (int i = 0; i < roles.size(); i++)
		{
			int index = roleIndices.get(roles.get(i));
			doeses.add(ProverQueryBuilder.toDoes(roles.get(i), moves.get(index)).toTerm());
		}
		return doeses;
	}
	
	/**
	 * Takes in a Legal Proposition and returns the appropriate corresponding Move
	 * @param p
	 * @return a PropNetMove
	 */
	public static Move getMoveFromProposition(Proposition p)
	{
		return new Move(p.getName().toSentence().get(1).toSentence());
	}
	
	/**
	 * Helper method for parsing the value of a goal proposition
	 * @param goalProposition
	 * @return the integer value of the goal proposition
	 */	
    private int getGoalValue(Proposition goalProposition)
	{
		GdlRelation relation = (GdlRelation) goalProposition.getName().toSentence();
		GdlConstant constant = (GdlConstant) relation.get(1);
		return Integer.parseInt(constant.toString());
	}
	
	/**
	 * A Naive implementation that computes a PropNetMachineState
	 * from the true BasePropositions.  This is correct but slower than more advanced implementations
	 * You need not use this method!
	 * @return PropNetMachineState
	 */	
	public MachineState getStateFromBase()
	{
		Set<GdlSentence> contents = new HashSet<GdlSentence>();
		for (int i : transMap.keySet())
		{
			if (boolState[i])contents.add(transMap.get(i));
		}
		return new MachineState(contents);
	}
	
	boolean shouldIgnore(Component comp){
		boolean fixed = true;
		for(Component in : comp.getInputs()){
			if(!(in instanceof util.propnet.architecture.components.Constant)){
				fixed = false;
			}
		}
		return fixed||(comp instanceof util.propnet.architecture.components.Constant) ||
				(comp.equals(propNet.getInitProposition()))||
				(comp.equals(propNet.getTerminalProposition()))||
				propNet.getGoalPropositions().containsValue(comp);
				
	}
	
	/*
	 * Checks to see if this game is disjunctively factorable.
	 * returns the number of factored games 
	 */
	@Override
	public int factorDisjunctiveGoalStates(Role role) {
		PrintWriter fout;
		
		goalOrdering = null;
		Set<Proposition> goalProps = propNet.getGoalPropositions().get(role);
		Proposition bestGoal = null;
		int bestVal = 0;
		//any goal proposition with an or gate could lead to disjunction
		//only focus on the goal which gets us the best reward
		for (Proposition goalProp : goalProps){
			if (goalProp.getSingleInput() instanceof Or) {
				System.out.println("Here's a potential disjunction"+goalProp.toString());
				System.out.println(goalProp.getSingleInput().getInputs().size());
				//goalProp.getSingleInput().getInputs().size();
				if(bestVal < getGoalValue(goalProp)){
					bestGoal = goalProp;
					bestVal = getGoalValue(goalProp);
				}
			} else {
				System.out.println("regular goal"+goalProp.toString());
			}
		}
		
		//there are up to n factors, where n is the number of inputs to the goal prop
		factors = new HashMap<Component, Set<Component>>();
		if(bestGoal == null) return 0;
		
		//make a set of all propositions affecting each input
		for(Component factorGoal : bestGoal.getSingleInput().getInputs()){
			Set<Component> f = new HashSet<Component>();
			Set<Component> fringe = new HashSet<Component>();
			f.add(factorGoal);
			fringe.add(factorGoal);
			System.out.println(factorGoal);
			//iterate until all connected factors are in the set
			//VERY INEFFICIENT!!!
			while(true){
				Set<Component> newFringe = new HashSet<Component>();
				for(Component comp : fringe){
					if(!(comp instanceof util.propnet.architecture.components.Constant) &&
							(f.size() == 1 || !comp.equals(factorGoal))){
						f.add(comp);
						for(Component in : comp.getInputs()){
							//we must cut out the init proposition
							if(!in.equals(propNet.getInitProposition()) && !f.contains(in))
								newFringe.add(in);
						}
					}	
				}
				fringe = newFringe;
				//if we didn't add anything this round, we're done
				if(fringe.size() == 0) break;
			}	
			factors.put(factorGoal, f);
		}
		
		//print to file for debugging
		try {
			fout = new PrintWriter(new FileWriter("out.txt"));
			fout.println(factors.size());
		
		//check for overlap of the generated sets
		List<Component> keys = new ArrayList<Component>(factors.keySet());
		System.out.println(factors.size());
		Map<Component, Set<Component>> oldFactors = new HashMap<Component, Set<Component>>(factors);
		factors.clear();
		for(int i = 0; i < keys.size(); i++){
			boolean noMatch = true;
			for(int j = i+1; j < keys.size(); j++){
				Set<Component> copy = new HashSet<Component>(oldFactors.get(keys.get(i)));
				copy.retainAll(oldFactors.get(keys.get(j)));
				System.out.println("comparison made");
				if(copy.size() > 0){
					fout.print("OVERLAP: ");
					fout.println(copy);
					System.out.println("removed an overlapping factor");
					noMatch = false;
					break;
				}
			}
			if(noMatch) factors.put(keys.get(i), oldFactors.get(keys.get(i)));			
		}
		
		//select the simplest game, but prepare data for all of them
		System.out.println(factors.size());
		if(factors.size() > 1){
			goalOrdering = new LinkedList<Component>();
			factorLegalsMap = new HashMap<Component, Set<Integer>>();
			for(Component key: factors.keySet()){
				//put the goals in order of complexity
				if(goalOrdering.size() == 0){
					goalOrdering.addFirst(key);
				}
				else{
					for(int i = 0; i < goalOrdering.size(); i++){
						if(factors.get(key).size() < factors.get(goalOrdering.get(i)).size()){
							goalOrdering.add(i, key);
						}
					}
					if(!goalOrdering.contains(key)) goalOrdering.addLast(key);
				}					
				
				Set<Integer> factorLegals = new HashSet<Integer>();
				for(Component comp : factors.get(key)){
					if(propNet.getLegalInputMap().containsKey(comp)){
						factorLegals.add(propNet.getLegalInputMap().get(comp).bitIndex);
					}
				}
				factorLegalsMap.put(key, factorLegals);
			}
			fout.println("goalOrdering: "+goalOrdering.toString());
		}
		
		fout.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return factors.size();		
	}
	
	@Override
	public void setHeuristicValues(Role role){
		heuristicMap = new HashMap<Integer, Double>();
		Set<Proposition> goalProps = propNet.getGoalPropositions().get(role);
		int bestVal = 0;
		Proposition bestGoal = null;
		//any goal proposition with an or gate could lead to disjunction
		//only focus on the goal which gets us the best reward
		for (Proposition goalProp : goalProps){
			if(bestVal < getGoalValue(goalProp)){
				bestVal = getGoalValue(goalProp);
				bestGoal = goalProp;
			}
		}
		//heuristicRecursion(bestGoal, ((double)getGoalValue(bestGoal)));
		int discount = bestVal/2;
		for(Proposition goalProp: goalProps){
			heuristicRecursion(goalProp, ((double)getGoalValue(goalProp))-discount);		
		}
	}
	
	private void heuristicRecursion(Component root, double val){
		if(root instanceof util.propnet.architecture.components.Transition){
			return;
		}
		if(root instanceof Proposition){
			if(heuristicMap.containsKey(root.bitIndex)){
				heuristicMap.put(root.bitIndex, heuristicMap.get(root.bitIndex) + val);
			}
			else heuristicMap.put(root.bitIndex, val);
		}
		Set<Component> inputs = root.getInputs();
		for(Component in : inputs){
			if(in instanceof util.propnet.architecture.components.Or){
				heuristicRecursion(in, val/2/inputs.size());
			}
			else if(in instanceof util.propnet.architecture.components.And){
				heuristicRecursion(in, val);
			}
			else if(in instanceof util.propnet.architecture.components.Not){
				heuristicRecursion(in, -val);
			}
			else{
				heuristicRecursion(in, val/inputs.size());
			}
		}		
	}

	public class AuxNode {
		public AuxNode() {}
		public AuxNode(Proposition prop, boolean mark) {
			this.proposition = prop;
			this.mark = mark;
			this.next = new ArrayList<AuxNode>();
		}

		public boolean equals(AuxNode node) {
			return this.proposition.equals(node.proposition) && this.mark == node.mark;
		}


		public Proposition proposition;
		public boolean mark;
		public List<AuxNode> next;
	}

	/*
	 * Returns whether or not list contains node. If remove is true, then node will be removed from list if it is contained in it.
	 */
	private boolean listContainsNode(List<AuxNode> list, AuxNode node, boolean remove) {
		for (AuxNode auxNode : list) {
			if (auxNode.equals(node)) {
				return true;
			}
		}
		return false;
	}

	/*
	 * Finds a cycle
	 */
	private boolean findCycle(AuxNode node, List<AuxNode> nextNodes, List<AuxNode> cycleNodes, List<AuxNode> allCheckedNodes) {
		for (AuxNode nextNode : nextNodes) {
			if (node.equals(nextNode)) {
				return true;
			}
			if (!listContainsNode(allCheckedNodes, nextNode, false) && !listContainsNode(cycleNodes, nextNode, false)) {
				allCheckedNodes.add(nextNode);
				cycleNodes.add(nextNode);
				if (findCycle(node, nextNode.next, cycleNodes, allCheckedNodes)) {
					return true;
				}
				cycleNodes.remove(nextNode);
			}
		}
		return false;
	}

	private boolean findGoal(AuxNode goal, List<AuxNode> nextNodes, List<AuxNode> checkedNodes) {
		for (AuxNode nextNode : nextNodes) {
			if (nextNode.equals(goal.proposition)) {
				return true;
			}
			if (!listContainsNode(checkedNodes, nextNode, false)) {
				checkedNodes.add(nextNode);
				if (findGoal(goal, nextNode.next, checkedNodes)) {
					return true;
				}
			}
		}
		return false;
	}

	private void findLatchInhibiters(List<AuxNode> auxGraph, Role role) {
		List<Proposition> goodGoals = new ArrayList<Proposition>();
		List<Proposition> badGoals = new ArrayList<Proposition>();
		for (Proposition goal : propNet.getGoalPropositions().get(role)) {
			if (getGoalValue(goal) == 100) {
				goodGoals.add(goal);
			} else if (getGoalValue(goal) == 0) {
				badGoals.add(goal);
			}
		}

		//Find latches
		for (AuxNode node : auxGraph) {
			List<AuxNode> cycleNodes = new ArrayList<AuxNode>();
			cycleNodes.add(node);
			List<AuxNode> allCheckedNodes = new ArrayList<AuxNode>();
			allCheckedNodes.add(node);
			if (findCycle(node, node.next, cycleNodes, allCheckedNodes)) {
				int numBaseProps = 0;
				for (AuxNode cycleNode : cycleNodes) {
					if (propNet.getBasePropositions().values().contains(cycleNode.proposition)) {
						numBaseProps++;
						if (numBaseProps > 1) {
							break;
						}
					}
				}
				if (numBaseProps == 1) {
					//Determine if latch is inhibiter
					for (Proposition goodGoal : goodGoals) {
						List<AuxNode> checkedNodes = new ArrayList<AuxNode>();
						checkedNodes.add(node);
						if (findGoal(new AuxNode(goodGoal, false), node.next, checkedNodes)) {
							if (node.mark) {
								printf(node.mark + node.proposition.toString() + "Inhibts " + goodGoal.toString());
								latches.add(node.proposition);
							} else {
								printf(node.mark + node.proposition.toString() + "implies " + goodGoal.toString());
								falseLatches.add(node.proposition);
							}

						}
					}

					for (Proposition badGoal : badGoals) {
						List<AuxNode> checkedNodes = new ArrayList<AuxNode>();
						checkedNodes.add(node);
						if (findGoal(new AuxNode(badGoal, true), node.next, checkedNodes)) {
							if (node.mark) {
								printf(node.mark + node.proposition.toString() + "Is a requirement for " + badGoal.toString());
								latches.add(node.proposition);
							} else {
								printf(node.mark + node.proposition.toString() + "Is an antirequirement " + badGoal.toString());
								falseLatches.add(node.proposition);
							}

						}
					}
				}
			}
		}
	}

	private void addNextProposition(AuxNode node, boolean inputMark, Component gate, Map<Proposition, AuxNode> trueNodes, Map<Proposition, AuxNode> falseNodes) {			
		for (Component output : gate.getOutputs()) {
			if (output instanceof Proposition) {
				if (inputMark) {
					node.next.add(trueNodes.get(output));
				} else {
					node.next.add(falseNodes.get(output));
				}
			} else if (output instanceof util.propnet.architecture.components.Not) {
				addNextProposition(node, !inputMark, output, trueNodes, falseNodes);
			} else if (output instanceof util.propnet.architecture.components.Or) {
				if (inputMark) {
					addNextProposition(node, inputMark, output, trueNodes, falseNodes);
				}
			} else if (output instanceof util.propnet.architecture.components.And) {
				if (!inputMark) {
					addNextProposition(node, inputMark, output, trueNodes, falseNodes);
				}
			} else {
				addNextProposition(node, inputMark, output, trueNodes, falseNodes);
			}
		}
	}

	@Override
	public void deadStateRemoval(Role role) {
		List<AuxNode> auxGraph = new ArrayList<AuxNode>();
		Map<Proposition, AuxNode> trueNodes = new HashMap<Proposition, AuxNode>();
		Map<Proposition, AuxNode> falseNodes = new HashMap<Proposition, AuxNode>();

		//Add a marked and unmarked node for each proposition into graph
		for (Proposition prop : propNet.getBasePropositions().values()) {
			AuxNode trueNode = new AuxNode(prop, true);
			auxGraph.add(trueNode);
			trueNodes.put(prop, trueNode);

			AuxNode falseNode = new AuxNode(prop, false);
			auxGraph.add(falseNode);
			falseNodes.put(prop, falseNode);
		}
		for (Component c : ordering) {
			if(c instanceof Proposition){
				Proposition prop = (Proposition) c;
				AuxNode trueNode = new AuxNode(prop, true);
				auxGraph.add(trueNode);
				trueNodes.put(prop, trueNode);

				AuxNode falseNode = new AuxNode(prop, false);
				auxGraph.add(falseNode);
				falseNodes.put(prop, falseNode);
			}

		}

		printf("Size of graph: " + auxGraph.size());

		for (int i = 0; i < trueNodes.size(); i++) {
			//Propagate truth values of marked nodes
			AuxNode markedNode = auxGraph.get(2*i);	
			AuxNode unmarkedNode = auxGraph.get(2*i + 1);
			for (Component output : markedNode.proposition.getOutputs()) {
				if (output instanceof Proposition) {
					markedNode.next.add(trueNodes.get(output));
					unmarkedNode.next.add(falseNodes.get(output));
				} else if (output instanceof util.propnet.architecture.components.Not) {
					addNextProposition(markedNode, false, output, trueNodes, falseNodes);
					addNextProposition(unmarkedNode, true, output, trueNodes, falseNodes);
				} else if (output instanceof util.propnet.architecture.components.Or) {
					addNextProposition(markedNode, true, output, trueNodes, falseNodes);		
				} else if (output instanceof util.propnet.architecture.components.And) {
					addNextProposition(unmarkedNode, false, output, trueNodes, falseNodes);
				} else {
					addNextProposition(markedNode, true, output, trueNodes, falseNodes);
					addNextProposition(unmarkedNode, false, output, trueNodes, falseNodes);
				}
			}
		}

		findLatchInhibiters(auxGraph, role);		

		printf("dead state removal complete!");
	}

	@Override
	public boolean stateIsDead(MachineState state) {
		Map<GdlTerm, Proposition> baseMap = propNet.getBasePropositions();
		for (Proposition falseLatch : falseLatches) {
			if (!baseMap.values().contains(falseLatch)) {
				return true;
			}
		}
		for (GdlSentence s : state.getContents()) {
			Proposition base = baseMap.get(s.toTerm());
			if (latches.contains(base)) {
				return true;
			}
		}
		return false;
	}
	
	public void printf(String string) {
		System.out.println(string);
	}

}