package player.gamer.statemachine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import util.statemachine.MachineState;
import util.statemachine.Move;
import util.statemachine.Role;
import util.statemachine.StateMachine;
import util.statemachine.exceptions.GoalDefinitionException;
import util.statemachine.exceptions.MoveDefinitionException;
import util.statemachine.exceptions.TransitionDefinitionException;
import util.statemachine.implementation.propnet.SamplePropNetStateMachine;
import util.statemachine.implementation.prover.ProverStateMachine;

public abstract class HeuristicGamer extends StateMachineGamer {
	//defines the heuristic used to value a state
	public abstract double getHeuristic(MachineState state, long timeout) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException;
	public abstract double getHeuristicPOST(MachineState state, long timeout) throws TransitionDefinitionException, MoveDefinitionException, GoalDefinitionException;
	public abstract void heuristicMetagame(long timeout) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException;
	
	//names the player
	public abstract String getName();

	protected static final int MAX_SCORE = 100;
	private static final int CALCULATION_BUFFER = 1000;

	protected long _stopTime;
	private int _levelsToExpand;
	protected List<Role> _oppRoles;
	protected Map<MachineState, List<Move>> _legalMoveCache = new HashMap<MachineState, List<Move>>();
	protected Map<StateAndMove, List<MachineState>> _nextStateCache = new HashMap<StateAndMove, List<MachineState>>();

	public class Move_Node {
		public double value;
		public Move move;
		public Move_Node(double value, Move move){
			this.value = value;
			this.move = move;
		}
	}
	
	private class StateAndMove {
		private MachineState state;
		private Move move;
		public StateAndMove(MachineState state, Move move) {
			this.state = state;
			this.move = move;
		}
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((move == null) ? 0 : move.hashCode());
			result = prime * result + ((state == null) ? 0 : state.hashCode());
			return result;
		}
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			StateAndMove other = (StateAndMove) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (move == null) {
				if (other.move != null)
					return false;
			} else if (!move.equals(other.move))
				return false;
			if (state == null) {
				if (other.state != null)
					return false;
			} else if (!state.equals(other.state))
				return false;
			return true;
		}
		private HeuristicGamer getOuterType() {
			return HeuristicGamer.this;
		}
		
	}

	@Override
	public StateMachine getInitialStateMachine() {	
		return new ProverStateMachine();
		//return new SamplePropNetStateMachine();
	}

	@Override
	public void stateMachineAbort() {}

	@Override
	public void stateMachineMetaGame(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {
		_oppRoles = new ArrayList<Role>();
		for (Role role : getStateMachine().getRoles()) {
			if (!role.equals(getRole())) {
				_oppRoles.add(role);
			}
		}
		_levelsToExpand = 1;
		long timeoutEarly = timeout - 1000;
		while (System.currentTimeMillis() < timeoutEarly) {
			maxScore(getCurrentState(), 0, timeoutEarly);
			_levelsToExpand++;
		}
		System.out.println("done metagaming");
		heuristicMetagame(_stopTime);
	}

	@Override
	public Move stateMachineSelectMove(long timeout)
			throws TransitionDefinitionException, MoveDefinitionException,
			GoalDefinitionException {

		_stopTime = timeout - CALCULATION_BUFFER;

		long currTime = System.currentTimeMillis();
		long timeAllocatedPRE = (timeout-currTime)/4; //DETERMINES THE TIME ALLOCATED FOR PRE STUFF
		//System.out.println("Time ALlocated:" + timeAllocatedPRE);
		
		List<Move> legalMoves;
		if (_legalMoveCache.containsKey(getCurrentState())) {
			legalMoves = _legalMoveCache.get(getCurrentState());
		} else {
			legalMoves = getStateMachine().getLegalMoves(getCurrentState(), getRole());
			_legalMoveCache.put(getCurrentState(), legalMoves);
		}
		_levelsToExpand = 2;
		List<Double> moveScores = getMove(getCurrentState(), currTime + timeAllocatedPRE, legalMoves);
		double highestScore = 0;
		for (Double score : moveScores) {
			if (score > highestScore) {
				highestScore = score;
			}
		}
		double scale = 100.0 / highestScore;
		
		//System.out.println("Pre->Post");
		_levelsToExpand = 0;
		List<Double> moveScoresPOST = getMovePOST(getCurrentState(), timeout, legalMoves);

		if(moveScores.isEmpty() && moveScoresPOST.isEmpty()){
		//	System.out.println("FAILED TO GET MOVE");
			return getStateMachine().getRandomMove(getCurrentState(), getRole());
		}

		int indexOfBestScore = 0;
		double bestscore = 0;
		for(int i = 0; i<legalMoves.size(); i++) {
			double score = 0;
			if (moveScores.size() > i) {
				score += (moveScores.get(i) * scale * 1)/3;    //RANDOM RATIO FOR HEURISTICS VS MONTE
			}
			if (moveScoresPOST.size() > i) {
				score += ((moveScoresPOST.get(i)+100) * 2)/3;  //THIS IS THE MONTE RATIO PART
			}			
			if (score > bestscore) {
				indexOfBestScore = i;
				bestscore = score;
			}
		}
		
		//	System.out.println("pre "+i+" : " + moveScores.get(i));
		//	System.out.println("post "+i+" : " + moveScoresPOST.get(i));
		//	System.out.println("score "+i+" : " + finalScore.get(i));

		return legalMoves.get(indexOfBestScore);
	}	

	/*
	 * Selects the move with the highest minimax value from the available moves
	 * for this state.  This is essentially a copy of maxScore which tracks moves.
	 */
	private List<Double> getMove(MachineState currState, long timeout, List<Move> legalMoves) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		if(getStateMachine().isTerminal(currState)){
			return new ArrayList<Double>();
		}
		List<Double> ScoreList = new ArrayList<Double>();
		long curr_time = System.currentTimeMillis();
		long time_step = (timeout-curr_time)/legalMoves.size();

		//Put minScore for each legal move into array and return array
		for(int i = 0; i<legalMoves.size(); i++){  //PREPROCESSING (IE NON-MONTE CARLO HEURISTICS)
			ScoreList.add(minScore(legalMoves.get(i), currState, 0, curr_time + (i+1)*time_step));
		}
		return ScoreList;
	}

	/*
	 * Function to control the depth of expansion.  
	 * Currently not very interesting.
	 */
	private boolean stopExpanding(MachineState state, int level, long timeout){
		return (System.currentTimeMillis() >= timeout-CALCULATION_BUFFER 
				|| level > _levelsToExpand);
	}

	/*
	 * Gets the max possible score for a given role at this state
	 * Level is the number of times to allow recursion, at this level
	 * we use the heuristic value of the state.
	 */
	private double maxScore(MachineState state, int level, long timeout) throws GoalDefinitionException, TransitionDefinitionException, MoveDefinitionException{
		if(getStateMachine().isTerminal(state)){ //base case 
			//System.out.println("terminal");
			return getStateMachine().getGoal(state, getRole());
		}
		if(stopExpanding(state, level, timeout)) {
		//	System.out.println("heuristic");
			return getHeuristic(state, timeout); 
		}
		
		
		List<Move> legalMoves;
		if (_legalMoveCache.containsKey(state)) {
			legalMoves = _legalMoveCache.get(state);
		} else {
			legalMoves = getStateMachine().getLegalMoves(state, getRole());
			_legalMoveCache.put(state, legalMoves);
		}
		
		long curr_time = System.currentTimeMillis();
		long time_step = (timeout-curr_time)/legalMoves.size();
	//	System.out.println("timestep_inmax: "+time_step);

		double maxVal = 0;
		//choose the move with the max value against a rational player
		for(int i = 0; i<legalMoves.size(); i++){
			Move move = legalMoves.get(i);
			double currVal = minScore(move, state, level, curr_time + (i+1)*time_step);
			if(System.currentTimeMillis() >= _stopTime) return getHeuristic(state, timeout);
			if(currVal > maxVal) maxVal = currVal;			
		}
		return maxVal;
	}
	
	/*
	 * Gets the minimum score a rational opponent would allow to be the value at
	 * this state
	 */
	private double minScore(Move move, MachineState state, int level, long timeout) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		double minVal = MAX_SCORE;
		//iterate over all possible joint moves, chose lowest scoring
		long curr_time = System.currentTimeMillis();
		//System.out.println("timestep_inmin: "+time_step);
		
		StateAndMove stateAndMove = new StateAndMove(state, move);
		List<MachineState> nextStates;
		if (_nextStateCache.containsKey(stateAndMove)) {
			nextStates = _nextStateCache.get(stateAndMove);
			long time_step = (timeout-curr_time)/nextStates.size();
			for (int i = 0; i < nextStates.size(); i++) {
				double currVal = maxScore(nextStates.get(i), level+1, curr_time + (i+1)*time_step);
				if(currVal < minVal) {
					minVal = currVal;
				}
			}
		} else {
			nextStates = new ArrayList<MachineState>();
			List<List<Move>> jointMoves = getStateMachine().getLegalJointMoves(state, getRole(), move);
			long time_step = (timeout-curr_time)/jointMoves.size();
			for(int i = 0; i<jointMoves.size(); i++) {
				MachineState nextState = getStateMachine().getNextState(state, jointMoves.get(i));
				nextStates.add(nextState);
				double currVal = maxScore(nextState, level+1, curr_time + (i+1)*time_step);
				if(currVal < minVal) {
					minVal = currVal;
				}
			}
			_nextStateCache.put(stateAndMove, nextStates);
		}
		
		return minVal;
	}

	/*
	 * Selects the move with the highest minimax value from the available moves
	 * for this state.  This is essentially a copy of maxScore which tracks moves.
	 */
	private List<Double> getMovePOST(MachineState currState, long timeout, List<Move> legalMoves) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		if(getStateMachine().isTerminal(currState)){
			return new ArrayList<Double>();
		}
		List<Double> ScoreList = new ArrayList<Double>();
		long curr_time = System.currentTimeMillis();
		long time_step = (timeout-curr_time)/legalMoves.size();

		//Put minScore for each legal move into array and return array
		for(int i = 0; i<legalMoves.size(); i++){  //POSTPROCESSING (IE MONTE CARLO HEURISTICS)
			ScoreList.add(minScorePOST(legalMoves.get(i), currState, 0, curr_time + (i+1)*time_step));
		}
		return ScoreList;
	}
	
	/*
	 * Gets the max possible score for a given role at this state
	 * Level is the number of times to allow recursion, at this level
	 * we use the heuristic value of the state.
	 */
	private double maxScorePOST(MachineState state, int level, long timeout) throws GoalDefinitionException, TransitionDefinitionException, MoveDefinitionException{
		if(getStateMachine().isTerminal(state)){ //base case 
		//	System.out.println("terminal");
			return getStateMachine().getGoal(state, getRole());
		}
		if(stopExpanding(state, level, timeout)) {
			//System.out.println("heuristic");
			return getHeuristicPOST(state, timeout); 
		}

		List<Move> legalMoves;
		if (_legalMoveCache.containsKey(state)) {
			legalMoves = _legalMoveCache.get(state);
		} else {
			legalMoves = getStateMachine().getLegalMoves(state, getRole());
			_legalMoveCache.put(state, legalMoves);
		}
		long curr_time = System.currentTimeMillis();
		long time_step = (timeout-curr_time)/legalMoves.size();
		//System.out.println("timestep_inmax: "+time_step);
		
		double maxVal = 0;
		//choose the move with the max value against a rational player
		for(int i = 0; i<legalMoves.size(); i++){
			Move move = legalMoves.get(i);
			double currVal = minScorePOST(move, state, level, curr_time + (i+1)*time_step);

			if(System.currentTimeMillis() >= _stopTime) return getHeuristicPOST(state, timeout);

			if(currVal > maxVal) maxVal = currVal;			
		}
		return maxVal;
	}
	
	/*
	 * Gets the minimum score a rational opponent would allow to be the value at
	 * this state
	 */
	private double minScorePOST(Move move, MachineState state, int level, long timeout) throws MoveDefinitionException, TransitionDefinitionException, GoalDefinitionException{
		double minVal = MAX_SCORE;
		//iterate over all possible joint moves, chose lowest scoring
		long curr_time = System.currentTimeMillis();
		//System.out.println("timestep_inmin: "+time_step);
		
		StateAndMove stateAndMove = new StateAndMove(state, move);
		List<MachineState> nextStates;
		if (_nextStateCache.containsKey(stateAndMove)) {
			nextStates = _nextStateCache.get(stateAndMove);
			long time_step = (timeout-curr_time)/nextStates.size();
			for (int i = 0; i < nextStates.size(); i++) {
				double currVal = maxScorePOST(nextStates.get(i), level+1, curr_time + (i+1)*time_step);
				if(currVal < minVal) {
					minVal = currVal;
				}
			}
		} else {
			nextStates = new ArrayList<MachineState>();
			List<List<Move>> jointMoves = getStateMachine().getLegalJointMoves(state, getRole(), move);
			long time_step = (timeout-curr_time)/jointMoves.size();
			for(int i = 0; i<jointMoves.size(); i++) {
				MachineState nextState = getStateMachine().getNextState(state, jointMoves.get(i));
				nextStates.add(nextState);
				double currVal = maxScorePOST(nextState, level+1, curr_time + (i+1)*time_step);
				if(currVal < minVal) {
					minVal = currVal;
				}
			}
			_nextStateCache.put(stateAndMove, nextStates);
		}
		return minVal;
	}

	@Override
	public void stateMachineStop() {
	}
}