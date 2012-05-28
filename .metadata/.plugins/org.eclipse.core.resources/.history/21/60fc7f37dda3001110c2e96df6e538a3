package util.statemachine.implementation.propnet;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.sun.org.apache.xpath.internal.operations.And;

import util.gdl.grammar.Gdl;
import util.gdl.grammar.GdlConstant;
import util.gdl.grammar.GdlProposition;
import util.gdl.grammar.GdlRelation;
import util.gdl.grammar.GdlSentence;
import util.gdl.grammar.GdlTerm;
import util.propnet.architecture.Component;
import util.propnet.architecture.PropNet;
import util.propnet.architecture.components.Or;
import util.propnet.architecture.components.Proposition;
import util.propnet.factory.OptimizingPropNetFactory;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.prover.query.ProverQueryBuilder;
import util.statemachine.implementation.prover.result.ProverResultParser;

@SuppressWarnings("unused")
public class SamplePropNetStateMachine extends StateMachine {
    /** The underlying proposition network  */
    private PropNet propNet;
    /** The topological ordering of the propositions */
    private List<Proposition> ordering;
    /** The player roles */
    private List<Role> roles;
    
    private MachineState initialState;
    private MachineState currentState;
    /**
     * Initializes the PropNetStateMachine. You should compute the topological
     * ordering here. Additionally you may compute the initial state here, at
     * your discretion.
     */
    @Override
    public void initialize(List<Gdl> description) {
        try {
			propNet = OptimizingPropNetFactory.create(description);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
        roles = propNet.getRoles();
        ordering = getOrdering();
        initialState = computeInitialState();
        System.out.println("order: "+ordering.toString());
        System.out.println("initState: "+initialState.toString());
    }    
    
    private MachineState computeInitialState()
	{
    	clearPropNet();
    	propNet.getInitProposition().setValue(true);//should be the only true proposition at start
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
        return propNet.getTerminalProposition().getValue();
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
            if(g.getValue()){
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
		factorDisjunctiveGoalStates();
		return initialState;
	}
	
	/**
	 * Computes the legal moves for role in state.
	 */
	@Override
	public List<Move> getLegalMoves(MachineState state, Role role)
	throws MoveDefinitionException {
		if(!state.equals(currentState)){
			clearPropNet();
			updateStateMachine(state);
		}
		//just check propositions corresponding to all possible moves for role
		//move is legal if the proposition is true
		Set<Proposition> legalProp = propNet.getLegalPropositions().get(role);
		List<Move> moves = new ArrayList<Move>();
		for(Proposition prop : legalProp){			
			if(prop.getValue())
				moves.add(getMoveFromProposition(prop));
		}
		
		return moves;
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
			termToProps.get(m).setValue(true);
		}

		return updateStateMachine(state);
	}
	
	private void clearPropNet(){
		Set<Proposition> props = propNet.getPropositions();
		for(Proposition p : props){
			p.setValue(false);
		}
	}
    
    private MachineState updateStateMachine(MachineState state) {
		//map the state to base propositions
		Map<GdlTerm, Proposition> baseMap = propNet.getBasePropositions();
		for (GdlSentence s : state.getContents()) {
			baseMap.get(s.toTerm()).setValue(true);
		}
    	
    	//update the props in order
    	for(Proposition prop : ordering)
    		prop.setValue(prop.getSingleInput().getValue());
    	
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
	public List<Proposition> getOrdering()
	{
		  // List to contain the topological ordering.
	       List<Proposition> order = new LinkedList<Proposition>();

	       // All of the components in the PropNet
	       Set<Component> components = new HashSet<Component>(propNet.getComponents());
	       
	       Set<Component> solved = new HashSet<Component>();
	       solved.add(propNet.getInitProposition());
	       solved.addAll(propNet.getBasePropositions().values());
	       solved.addAll(propNet.getInputPropositions().values());
	       
	       int numToSolve = propNet.getPropositions().size() - solved.size();

	       while(order.size() < numToSolve){
	    	   Set<Component> nowSolved = new HashSet<Component>();
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
		            	   if(comp instanceof Proposition) order.add((Proposition)comp);
	                   }
	               }
	           }
	           solved.addAll(nowSolved);
	       }
	       return order;
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
		for (Proposition p : propNet.getBasePropositions().values())
		{
			p.setValue(p.getSingleInput().getValue());
			if (p.getValue())
			{
				contents.add(p.getName().toSentence());
			}

		}
		return new MachineState(contents);
	}
	
	public void factorDisjunctiveGoalStates() {
		Or orGate = new Or();
		Map<Role, Set<Proposition>> goalMap = propNet.getGoalPropositions();
		for (Role role : roles) {
			Set<Proposition> goalProps = goalMap.get(role);
			for (Proposition goalProp : goalProps) {
				if (goalProp.getSingleInput().getClass().equals(orGate.getClass())) {
					System.out.println("Here's a potential disjunction");
				} else {
					System.out.println("regular goal");
				}
			}
		}
	}
}