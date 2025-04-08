package main

import (
	"bufio"
	"fmt"
	"math"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"

	"github.com/notnil/chess"
	// "github.com/notnil/chess/opening/polyglot" // Removed as it's not found in the module
)

// Values are from White's POV. Swap number to negative for Black.

var pawnTable = [64]int{
	0, 0, 0, 0, 0, 0, 0, 0,
	50, 50, 50, 50, 50, 50, 50, 50,
	10, 10, 20, 30, 30, 20, 10, 10,
	5, 5, 10, 25, 25, 10, 5, 5,
	0, 0, 0, 20, 20, 0, 0, 0,
	5, -5, -10, 0, 0, -10, -5, 5,
	5, 10, 10, 20, 20, 10, 10, 5, // Adjusted 7th rank
	0, 0, 0, 0, 0, 0, 0, 0,
}

// Endgame pawn table - strongly encourages promotion
var pawnEndgameTable = [64]int{
	0, 0, 0, 0, 0, 0, 0, 0,
	100, 100, 100, 100, 100, 100, 100, 100, // High value for advanced pawns
	60, 60, 60, 60, 60, 60, 60, 60,
	40, 40, 40, 40, 40, 40, 40, 40,
	20, 20, 20, 30, 30, 20, 20, 20,
	10, 10, 10, 10, 10, 10, 10, 10,
	5, 5, 5, 5, 5, 5, 5, 5,
	0, 0, 0, 0, 0, 0, 0, 0,
}

var knightTable = [64]int{
	-50, -40, -30, -30, -30, -30, -40, -50,
	-40, -20, 0, 0, 0, 0, -20, -40,
	-30, 0, 10, 15, 15, 10, 0, -30,
	-30, 5, 15, 20, 20, 15, 5, -30,
	-30, 0, 15, 20, 20, 15, 0, -30,
	-30, 5, 10, 15, 15, 10, 5, -30,
	-40, -20, 0, 5, 5, 0, -20, -40,
	-50, -40, -30, -30, -30, -30, -40, -50,
}

var bishopTable = [64]int{
	-20, -10, -10, -10, -10, -10, -10, -20,
	-10, 0, 0, 0, 0, 0, 0, -10,
	-10, 0, 5, 10, 10, 5, 0, -10,
	-10, 5, 5, 10, 10, 5, 5, -10,
	-10, 0, 10, 10, 10, 10, 0, -10,
	-10, 10, 10, 10, 10, 10, 10, -10,
	-10, 5, 0, 0, 0, 0, 5, -10,
	-20, -10, -10, -10, -10, -10, -10, -20,
}

var rookTable = [64]int{
	0, 0, 0, 0, 0, 0, 0, 0,
	5, 10, 10, 10, 10, 10, 10, 5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	-5, 0, 0, 0, 0, 0, 0, -5,
	0, -5, 0, 5, 5, 0, -5, 0,
}

// Queen table is usually just the bishop + rook tables added together
var queenTable [64]int

var kingMidgameTable = [64]int{
	-30, -40, -40, -50, -50, -40, -40, -30,
	-30, -40, -40, -50, -50, -40, -40, -30,
	-30, -40, -40, -50, -50, -40, -40, -30,
	-30, -40, -40, -50, -50, -40, -40, -30,
	-20, -30, -30, -40, -40, -30, -30, -20,
	-10, -20, -20, -20, -20, -20, -20, -10,
	20, 20, 0, 0, 0, 0, 20, 20,
	20, 30, 10, 0, 0, 10, 30, 20,
}

// King endgame table - encourages king activity towards the center
var kingEndgameTable = [64]int{
	-50, -30, -30, -30, -30, -30, -30, -50,
	-30, -20, 0, 0, 0, 0, -20, -30,
	-30, -10, 20, 30, 30, 20, -10, -30,
	-30, -10, 30, 40, 40, 30, -10, -30,
	-30, -10, 30, 40, 40, 30, -10, -30,
	-30, -10, 20, 30, 30, 20, -10, -30,
	-30, -30, 0, 0, 0, 0, -30, -30,
	-50, -30, -30, -30, -30, -30, -30, -50,
}

func init() {
	for i := 0; i < 64; i++ {
		queenTable[i] = rookTable[i] + bishopTable[i]
	}
	// Initialize TT
	transpositionTable = make(map[[16]byte]TranspositionEntry, ttSizeEstimate) // Correct map key type
}

const (
	ExactScore = iota
	LowerBound // Alpha score (score is at least this good)
	UpperBound // Beta score (score is at most this good)
)

type TranspositionEntry struct {
	Hash      [16]byte
	Depth     int // Depth this position was searched to
	Score     int // Score found
	ScoreType int
	BestMove  *chess.Move // Best move found from this position
}

var transpositionTable map[[16]byte]TranspositionEntry
var ttSizeEstimate = 1000000
var ttMutex sync.Mutex

// Capturing a higher value piece with a lower value one is prioritized.
var orderValues = map[chess.PieceType]int{
	chess.Pawn:   1,
	chess.Knight: 3,
	chess.Bishop: 3,
	chess.Rook:   5,
	chess.Queen:  9,
	chess.King:   100, // King captures are rare but important (shouldn't happen legally)
}

// Uses MVV-LVA (Most Valuable Victim - Least Valuable Aggressor) for captures.
func scoreMove(board *chess.Board, move *chess.Move) int {
	// Check if it's a capture
	targetSq := move.S2() // Use S2() for the destination square
	victim := board.Piece(targetSq)

	if victim != chess.NoPiece {
		attacker := board.Piece(move.S1())                                            // Piece making the move
		return (orderValues[victim.Type()] * 10) - orderValues[attacker.Type()] + 100 // Add 100 base score for any capture
	}

	// Quiet moves get a score of 0
	return 0
}

// It helps mitigate the horizon effect.
func qsearch(pos *chess.Position, alpha, beta int) int {
	// Use the static evaluation as a baseline score
	standPatScore := evaluateBoard(pos) // Evaluate from the current player's perspective

	if standPatScore >= beta {
		return beta
	}

	if standPatScore > alpha {
		alpha = standPatScore
	}

	// Generate and score capture moves
	captureMoves := []*chess.Move{}
	board := pos.Board()
	for _, move := range pos.ValidMoves() {
		targetSq := move.S2()
		victim := board.Piece(targetSq)
		isEnPassant := move.HasTag(chess.EnPassant)
		// Consider captures and promotions in quiescence
		isPromotion := move.Promo() != chess.NoPieceType

		if victim != chess.NoPiece || isEnPassant || isPromotion {
			captureMoves = append(captureMoves, move)
		}
	}

	sort.SliceStable(captureMoves, func(i, j int) bool {
		return scoreMove(board, captureMoves[i]) > scoreMove(board, captureMoves[j])
	})

	for _, move := range captureMoves {
		nextPos := pos.Update(move)
		score := -qsearch(nextPos, -beta, -alpha)

		if score >= beta {
			return beta
		}
		if score > alpha {
			alpha = score
		}
	}

	// Return the best score found
	return alpha
}

// negamax implements the negamax algorithm with alpha-beta pruning and transposition table.
// It returns the score of the position relative to the player whose turn it is.
func negamax(pos *chess.Position, depth, alpha, beta int) int {
	originalAlpha := alpha // Store original alpha for TT storing logic
	hash := pos.Hash()

	ttMutex.Lock() // Lock before accessing TT
	entry, entryExists := transpositionTable[hash]
	ttMutex.Unlock() // Unlock after accessing TT

	if entryExists && entry.Depth >= depth {
		switch entry.ScoreType {
		case ExactScore:
			return entry.Score
		case LowerBound:
			if entry.Score > alpha {
				alpha = entry.Score // Raise alpha
			}
		case UpperBound:
			if entry.Score < beta {
				beta = entry.Score // Lower beta
			}
		} // This closes the switch statement
		if alpha >= beta {
			return entry.Score
		}
	}

	// Check for checkmate/stalemate *before* depth check.
	// The score must be relative to the player whose turn it is.
	outcome := pos.Status()
	if outcome != chess.NoMethod {
		switch outcome {
		case chess.Checkmate:
			// The current player is checkmated, return a very large negative score.
			return -99999 + (100 - depth) // Adjust score based on depth.
			// Otherwise, even if there is a possible checkmate a long way off, it will take it into too much consideration.
		case chess.Stalemate:
			return 0
		default:
			return 0
		}
	}

	// If depth limit is reached, start Quiescence Search.
	if depth == 0 {
		return qsearch(pos, alpha, beta) // Call quiescence search
	}

	maxScore := math.MinInt32 // Initialize with the lowest possible score
	var bestMoveInNode *chess.Move = nil
	validMoves := pos.ValidMoves()

	var ttMove *chess.Move = nil
	ttMutex.Lock()
	entry, entryExists = transpositionTable[hash] // Read again under lock if needed
	ttMutex.Unlock()
	if entryExists {
		ttMove = entry.BestMove
		if ttMove != nil {
			for i, mv := range validMoves {
				if mv.String() == ttMove.String() {
					// Swap ttMove to the front
					validMoves[0], validMoves[i] = validMoves[i], validMoves[0]
					break
				}
			}
		}
	}

	board := pos.Board() // Get board once for scoring
	startIdx := 0
	if ttMove != nil {
		startIdx = 1 // Don't re-sort the first element if it was the TT move
	}
	sort.SliceStable(validMoves[startIdx:], func(i, j int) bool {
		realI := i + startIdx
		realJ := j + startIdx
		// Sort in descending order of score (higher score first)
		return scoreMove(board, validMoves[realI]) > scoreMove(board, validMoves[realJ])
	})

	for _, move := range validMoves { // Iterate through sorted moves (with TT move first if found)
		nextPos := pos.Update(move)
		score := -negamax(nextPos, depth-1, -beta, -alpha)

		if score > maxScore {
			maxScore = score
			bestMoveInNode = move // Track the best move found in this node
		}
		if score > alpha {
			alpha = score
		}
		if alpha >= beta {
			entry = TranspositionEntry{ // Use = instead of :=
				Hash:      hash,
				Depth:     depth,
				Score:     beta,
				ScoreType: LowerBound,
				BestMove:  move, // Store the move that caused the cutoff
			}
			ttMutex.Lock() // Lock before writing to TT
			transpositionTable[hash] = entry
			ttMutex.Unlock() // Unlock after writing to TT
			return beta      // Return beta (fail-high)
		}
	}

	var scoreType int
	if maxScore <= originalAlpha {
		scoreType = UpperBound
	} else {
		scoreType = ExactScore
	}

	entry = TranspositionEntry{
		Hash:      hash,
		Depth:     depth,
		Score:     maxScore,
		ScoreType: scoreType,
		BestMove:  bestMoveInNode, // Store the best move found
	}
	ttMutex.Lock() // Lock before writing to TT
	transpositionTable[hash] = entry
	ttMutex.Unlock() // Unlock after writing to TT

	return maxScore
}

// Struct to hold results from parallel searches
type moveResult struct {
	move  *chess.Move
	score int
}

func findBestMove(game *chess.Game, depth int) *chess.Move {
	validMoves := game.ValidMoves()
	numMoves := len(validMoves)
	if numMoves == 0 {
		return nil // No moves available
	}

	bestScore := math.MinInt32
	var bestMove *chess.Move = nil

	alpha := math.MinInt32
	beta := math.MaxInt32

	board := game.Position().Board() // Get board once for scoring
	sort.SliceStable(validMoves, func(i, j int) bool {
		// Sort in descending order of score (higher score first)
		return scoreMove(board, validMoves[i]) > scoreMove(board, validMoves[j])
	})

	resultsChan := make(chan moveResult, numMoves) // Buffered channel
	var wg sync.WaitGroup

	fmt.Printf("Launching %d goroutines for root search...\n", numMoves) // Debug
	for i, move := range validMoves {
		wg.Add(1)
		currentMove := move
		moveIndex := i
		go func(m *chess.Move, index int) {
			defer wg.Done()
			nextPos := game.Position().Update(m)

			score := -negamax(nextPos, depth-1, -beta, -alpha) // Use root alpha/beta

			// Send result back
			resultsChan <- moveResult{move: m, score: score}

		}(currentMove, moveIndex)
	}

	go func() {
		wg.Wait()
		close(resultsChan)
	}()

	// Small penalty for choosing a move that leads directly to threefold repetition
	const repetitionPenalty = -30 // If it's this close, it's really anyone's game still.

	fmt.Println("Waiting for results...") // Debug
	for result := range resultsChan {
		currentScore := result.score

		// Simulate the move on a temporary game copy
		tempGame := chess.NewGame(chess.UseNotation(chess.AlgebraicNotation{})) // Use same notation
		for _, histMove := range game.Moves() {
			_ = tempGame.Move(histMove) // Replay history - ignore errors for simplicity here
		}
		err := tempGame.Move(result.move) // Apply the potential move

		if err == nil { // Check if the move was valid in the temp game
			outcome := tempGame.Outcome()
			method := tempGame.Method()
			if outcome == chess.Draw && method == chess.ThreefoldRepetition {
				fmt.Printf("  * Move %s leads to threefold repetition draw, applying penalty %d\n", result.move, repetitionPenalty)
				currentScore += repetitionPenalty // Apply penalty
			}
		} else {
			// This case should ideally not happen if result.move came from game.ValidMoves()
			fmt.Printf("Warning: Could not apply move %s to temp game simulation: %v\n", result.move, err)
		}

		fmt.Printf("  * Result received for move %s -> original_score %d, adjusted_score %d\n", result.move, result.score, currentScore) // Debug output
		if currentScore > bestScore {
			bestScore = currentScore // Use the potentially adjusted score for comparison
			bestMove = result.move
		}
	}
	fmt.Println("Finished collecting results.") // Debug

	if bestMove == nil && numMoves > 0 {
		// Should not happen if there are valid moves, but as a backup
		fmt.Println("Warning: No best move found, returning first valid move.")
		return validMoves[0]
	}

	fmt.Printf("Engine chooses: %s (Score: %d)\n", bestMove, bestScore)
	return bestMove
}

const (
	rookOpenFileBonus        = 15   // Bonus for rook on a file with no pawns
	rookSemiOpenFileBonus    = 10   // Bonus for rook on a file with only opponent pawns
	endgameMaterialThreshold = 1500 // Threshold for endgame detection (e.g., sum of piece values excluding kings)
)

func isEndgame(board *chess.Board) bool {
	materialCount := 0
	pieceValues := map[chess.PieceType]int{
		chess.Pawn:   100,
		chess.Knight: 320,
		chess.Bishop: 330,
		chess.Rook:   500,
		chess.Queen:  900,
	} // Exclude King

	for sq := chess.A1; sq <= chess.H8; sq++ {
		piece := board.Piece(sq)
		if piece != chess.NoPiece && piece.Type() != chess.King {
			materialCount += pieceValues[piece.Type()]
		}
	}
	return materialCount < endgameMaterialThreshold
}

func evaluateBoard(pos *chess.Position) int {
	method := pos.Status()
	if method == chess.Checkmate {
		if pos.Turn() == chess.White {
			return -99999
		} // White is checkmated
		return 99999 // Black is checkmated
	}
	if method == chess.Stalemate || method == chess.DrawOffer || method == chess.FiftyMoveRule || method == chess.InsufficientMaterial || method == chess.ThreefoldRepetition {
		return 0 // Draw
	}

	board := pos.Board()
	score := 0
	inEndgame := isEndgame(board) // Check if it's endgame

	pieceValues := map[chess.PieceType]int{
		chess.Pawn:   100,
		chess.Knight: 320,
		chess.Bishop: 330,
		chess.Rook:   500,
		chess.Queen:  900,
		chess.King:   20000,
	}

	for sq := chess.A1; sq <= chess.H8; sq++ {
		piece := board.Piece(sq)
		if piece == chess.NoPiece {
			continue
		}

		value := pieceValues[piece.Type()]
		sqIndex := int(sq)
		pstValue := 0 // Initialize PST value

		// Get the base PST value from White's perspective table, considering game phase
		switch piece.Type() {
		case chess.Pawn:
			if inEndgame {
				pstValue = pawnEndgameTable[sqIndex]
			} else {
				pstValue = pawnTable[sqIndex]
			}
		case chess.Knight:
			pstValue = knightTable[sqIndex] // Knight table often used throughout
		case chess.Bishop:
			pstValue = bishopTable[sqIndex]
		case chess.Rook:
			pstValue = rookTable[sqIndex]
		case chess.Queen:
			pstValue = queenTable[sqIndex] // Queen uses combined rook/bishop
		case chess.King:
			if inEndgame {
				pstValue = kingEndgameTable[sqIndex]
			} else {
				pstValue = kingMidgameTable[sqIndex]
			}

		}

		rookBonus := 0
		if piece.Type() == chess.Rook {
			file := sq.File()
			myPawnsOnFile := 0
			opponentPawnsOnFile := 0
			// Check the file for pawns
			for rank := chess.Rank1; rank <= chess.Rank8; rank++ {
				// Calculate square index directly instead of using NewSquare
				pawnSq := chess.Square(int(file) + int(rank)*8)
				p := board.Piece(pawnSq)
				if p.Type() == chess.Pawn {
					if p.Color() == piece.Color() {
						myPawnsOnFile++
					} else {
						opponentPawnsOnFile++
					}
				}
			}
			if myPawnsOnFile == 0 {
				if opponentPawnsOnFile == 0 {
					rookBonus = rookOpenFileBonus // Open file
				} else {
					rookBonus = rookSemiOpenFileBonus // Semi-open file (only opponent pawns)
				}
			}
		}

		// Adjust score based on piece color
		if piece.Color() == chess.White {
			score += value
			score += pstValue  // Add White PST value (from white's perspective table)
			score += rookBonus // Add rook bonus for White
		} else { // Black piece
			score -= value
			// For Black, calculate the flipped square index for PST lookup
			flippedSqIndex := (7-(sqIndex/8))*8 + (sqIndex % 8)
			blackPstValue := 0
			// Get the PST value from the *same* table but using the flipped index, considering game phase
			switch piece.Type() {
			case chess.Pawn:
				if inEndgame {
					blackPstValue = pawnEndgameTable[flippedSqIndex]
				} else {
					blackPstValue = pawnTable[flippedSqIndex]
				}
			case chess.Knight:
				blackPstValue = knightTable[flippedSqIndex]
			case chess.Bishop:
				blackPstValue = bishopTable[flippedSqIndex]
			case chess.Rook:
				blackPstValue = rookTable[flippedSqIndex]
			case chess.Queen:
				blackPstValue = queenTable[flippedSqIndex]
			case chess.King:
				if inEndgame {
					blackPstValue = kingEndgameTable[flippedSqIndex]
				} else {
					blackPstValue = kingMidgameTable[flippedSqIndex]
				}
			}
			// Subtract the value from the table entry corresponding to the flipped square
			score -= blackPstValue
			score -= rookBonus
		}
	}

	// Return score relative to the side to move
	if pos.Turn() == chess.White {
		return score
	}
	// If it's Black's turn, negate the score (a high positive score for White is bad for Black)
	return -score
}

func main() {
	reader := bufio.NewReader(os.Stdin)
	var playerColor chess.Color
	var searchDepth int

	for {
		fmt.Print("Choose your color (white or black): ")
		input, _ := reader.ReadString('\n')
		input = strings.TrimSpace(strings.ToLower(input))
		if input == "white" {
			playerColor = chess.White
			break
		} else if input == "black" {
			playerColor = chess.Black
			break
		} else {
			fmt.Println("Invalid input. Please enter 'white' or 'black'.")
		}
	}

	for {
		fmt.Print("Enter engine search depth (6 or 7 recomended): ")
		input, _ := reader.ReadString('\n')
		input = strings.TrimSpace(input)
		depth, err := strconv.Atoi(input)
		if err == nil && depth > 0 {
			searchDepth = depth
			break
		} else {
			fmt.Println("Invalid input. Please enter a positive integer for the depth.")
		}
	}

	fmt.Printf("Starting game. You are %s. Engine depth: %d\n", playerColor, searchDepth)

	game := chess.NewGame()

	for game.Outcome() == chess.NoOutcome {
		fmt.Println("\n--------------------")
		fmt.Println(game.Position().Board().Draw())
		fmt.Printf("Turn: %s\n", game.Position().Turn())

		var move *chess.Move

		if game.Position().Turn() == playerColor {
			fmt.Print("Enter your move (e.g., e2e4): ")
			input, _ := reader.ReadString('\n')
			input = strings.TrimSpace(input)

			var playerMove *chess.Move
			var err error
			for _, m := range game.ValidMoves() {
				if m.String() == input {
					playerMove = m
					break
				}
			}

			if playerMove == nil {
				playerMove, err = chess.AlgebraicNotation{}.Decode(game.Position(), input)
				if err != nil {
					fmt.Printf("Invalid move")
					continue // Ask for input again
				}
			}

			isValid := false
			for _, validMove := range game.ValidMoves() {
				if playerMove.String() == validMove.String() {
					isValid = true
					break
				}
			}

			if !isValid {
				fmt.Printf("Illegal move")
				continue // Ask for input again
			}
			move = playerMove
			fmt.Printf("You moved: %s\n", move)

		} else {
			isEngineWhite := playerColor == chess.Black
			moveCount := len(game.Moves())

			if isEngineWhite && moveCount == 0 {
				// If engine is White and it's the first move, play e2e4
				forcedMove, err := chess.AlgebraicNotation{}.Decode(game.Position(), "e4")
				if err == nil {
					// Check if e4 is a valid move (it should be at the start)
					isValid := false
					for _, validMove := range game.ValidMoves() {
						if forcedMove.String() == validMove.String() {
							isValid = true
							break
						}
					}
					if isValid {
						move = forcedMove
						fmt.Println("Engine plays opening: e4")
					}
				}
				// If decoding/validation fails for some reason, fall back to normal search
				if move == nil {
					fmt.Println("Warning: Could not force e4, falling back to search.")
				}

			} else if !isEngineWhite && moveCount == 1 {
				// If engine is Black and it's the second move (opponent moved first)
				opponentMove := game.Moves()[0]
				if opponentMove.String() == "e2e4" {
					// If opponent played e2e4, play e7e5
					forcedMove, err := chess.AlgebraicNotation{}.Decode(game.Position(), "e5")
					if err == nil {
						// Check if e5 is a valid move
						isValid := false
						for _, validMove := range game.ValidMoves() {
							if forcedMove.String() == validMove.String() {
								isValid = true
								break
							}
						}
						if isValid {
							move = forcedMove
							fmt.Println("Engine plays opening response: e5")
						}
					}
					// If decoding/validation fails, fall back to normal search
					if move == nil {
						fmt.Println("Warning: Could not force e5, falling back to search.")
					}
				}
			}

			if move == nil { // If no opening move was forced, use the engine's calculation
				currentDepth := searchDepth
				if isEndgame(game.Position().Board()) {
					currentDepth++ // Increase depth by 1 in the endgame
					fmt.Printf("Engine is thinking... (Endgame depth: %d)\n", currentDepth)
				} else {
					fmt.Println("Engine is thinking...")
				}
				move = findBestMove(game, currentDepth)
			}

			if move == nil { // Check again after findBestMove
				fmt.Println("Engine has no moves available.")
				break
			}
			fmt.Printf("Engine moved: %s\n", move)
		}

		// Apply the move
		err := game.Move(move)
		if err != nil {
			fmt.Printf("Error applying move %s: %v\n", move, err)
			break
		}
	}

	fmt.Println("\n--------------------")
	fmt.Println("Game Over!")
	fmt.Println(game.Position().Board().Draw())
	fmt.Printf("Outcome: %s\n", game.Outcome())
	fmt.Printf("Method: %s\n", game.Method())
}
