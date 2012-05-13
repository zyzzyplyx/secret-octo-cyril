package player.gamer.statemachine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import util.game.Game;
import util.gdl.grammar.GdlSentence;
import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.prover.ProverStateMachine;

public class MiniMaxSMG extends StateMachineGamer {

	private static final int MAX_SCORE = 100;



	private Role _role;
	private List<Role> _opp_roles;
	private HashMap<MachineState,Integer> _cache;


	private class Move_Node {
		public int value;
		public Move move;
		public Move_Node(int value, Move move){
			this.value = value;
			this.move = move;
		}
	}
	
	@Override
	public StateMachine getInitialStateMachine() {
		StateMachine stateMachine = new ProverStateMachine();
		stateMachine.initialize(this.getMatch().getGame().getRules());
		return stateMachine;
	}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		_role = this.getRole();
		_opp_roles = new ArrayList<Role>();
		_cache = new HashMap<MachineState,Integer>();
		ArrayList<Role> all_roles = (ArrayList<Role>) this.getStateMachine().getRoles();
		for(int i=0; i<all_roles.size(); i++){
			if(!(_role.equals(all_roles.get(i)))){
				_opp_roles.add(all_roles.get(i));
			}
		}
		return;
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {

		try {
			return selectMove(this.getCurrentState());
		} catch (GoalDefinitionException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			return null;
		}
	}
	
	private Move selectMove(MachineState state) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		List<Move> legalMoves = this.getStateMachine().getLegalMoves(state, _role);
		if(legalMoves.size()==1){
			return(legalMoves.get(0));
		}
		return(getValue(state)).move;
	}
	
	private Move_Node getValue(MachineState currState) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		List<Move> legalMoves = this.getStateMachine().getLegalMoves(currState, _role);
		Move_Node best_node = new Move_Node(-1,null); 
		for(int i=0; i<legalMoves.size(); i++){
			List<List<Move> > jointMoves = this.getStateMachine().getLegalJointMoves(currState, _role, legalMoves.get(i));
			int value_worstcase = MAX_SCORE;
			for(int j=0; j<jointMoves.size(); j++){
				MachineState tempState = this.getStateMachine().getNextState(currState, jointMoves.get(j));
				int currvalue;
				if(this.getStateMachine().isTerminal(tempState)){
					//System.out.println("hey");
					currvalue = this.getStateMachine().getGoal(tempState, _role);
				} else if(_cache.containsKey(tempState)){
					currvalue = _cache.get(tempState);
					System.out.println("cache hit");
				} else {
					currvalue = getValue(tempState).value;
					_cache.put(tempState, currvalue);
				}
				if(currvalue<value_worstcase) {
					value_worstcase = currvalue;
				}
			}
			if(best_node.value<value_worstcase) {
				best_node.value = value_worstcase;
				best_node.move = legalMoves.get(i);
			}

		}

		return best_node;
	}

	@Override
	public void stateMachineStop() {
		// TODO Auto-generated method stub

	}

	@Override
	public void stateMachineAbort() {
		// TODO Auto-generated method stub

	}

}
