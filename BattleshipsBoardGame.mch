/* BattleshipsBoardGame
 * Author: Thenuka Dinujaya Ubayasena
 * Student_ID: 20201025
 * UoW_ID: w1840002
 * Creation date: 12/02/2024
 */
 
MACHINE
    BattleshipsBoardGame
    
SETS
    // Define two players: Player1 and Player2
    PLAYERS         = {Player1, Player2};
    
    // Output messages for the current game status
    GAME_STATUS     = {
                         Deploying, 
                         Ongoing, 
                         Player1_WON, 
                         Player2_WON
                      };
                      
    // Output messages for the player's shoots
    SCORES          = {
                         Hit,
                         Miss
                      };
    
    // Output messages for when the player deploying ships
    DEPLOY_STATUS   = {
                         Error_Ships_Overlapped,
                         Success_Ships_Deployed
                      }
                      
CONSTANTS
    GRID,                                                        // Represents the entire grid for the game board
    GRID_X_RANGE,                                                // Range of valid x-coordinates for the grid
    GRID_Y_RANGE,                                                // Range of valid y-coordinates for the grid
    FLEET_SIZE                                                   // Number of warships each player can deploy
    
PROPERTIES
    GRID_X_RANGE <: NAT1 & GRID_X_RANGE = 1..10 &         
    GRID_Y_RANGE <: NAT1 & GRID_Y_RANGE = 1..10 &
    GRID = GRID_X_RANGE * GRID_Y_RANGE &                         // The grid is defined as the Cartesian product of X and Y ranges
    FLEET_SIZE = 3                                               // Fleet size is fixed at 3 warships per player

VARIABLES
    player1_warships,                                            // positions of Player 1's warships
    player2_warships,                                            // positions of player 2's warships
    player1_hits,                                                // player1's hit positions
    player2_hits,                                                // Player2's hit positions 
    current_game_status,                                         // Current status of the game
    current_player,                                              // The player whose turn it is
    shots_taken                                                  // Number of shots taken by each player
    
INVARIANT
    // Conditions for the variables
    player1_warships <: GRID &                                    
    player2_warships <: GRID &
    card(player1_warships) <= FLEET_SIZE &                       // Player1 cannot exceed the fleet size
    card(player1_warships) <= FLEET_SIZE &                       // Player2 cannot exceed the fleet size
    player1_hits <: GRID &
    player2_hits <: GRID &
    player1_warships /\ player2_warships = {} &
    current_game_status : GAME_STATUS &
    current_player : PLAYERS &
    shots_taken : PLAYERS --> NAT                                // Number of shots
    
INITIALISATION
    // Initialising values for variables
    player1_warships := {} ||
    player2_warships := {} ||
    player1_hits := {} ||
    player2_hits := {} ||
    current_game_status := Deploying ||
    current_player := Player1 ||
    shots_taken := {Player1 |-> 0, Player2 |-> 0}                // Initialize shots taken to zero for both players
    
DEFINITIONS
    // These functions will be used to create the graph
    ANIMATION_FUNCTION == ({ row, col, img | row: GRID_X_RANGE & col: GRID_Y_RANGE & img = 0 });                                            // Empty grid
    ANIMATION_FUNCTION1 == ({ row, col, img | row: GRID_X_RANGE & col: GRID_Y_RANGE & (row |-> col) : player1_warships & img = 1 });        // Player1 warships
    ANIMATION_FUNCTION2 == ({ row, col, img | row: GRID_X_RANGE & col: GRID_Y_RANGE & (row |-> col) : player2_warships & img = 2 });        // Player2 warships
    
    // Images for animations
    ANIMATION_IMG0 == "images/empty.png";
    ANIMATION_IMG1 == "images/warship1.png";
    ANIMATION_IMG2 == "images/warship2.png";
    
OPERATIONS
    // Operation to deploy warships for each player
    report <-- deployFleet (player, positions) =
    PRE
        current_game_status = Deploying &
        player : PLAYERS &                        
        positions : GRID & positions : GRID &     
        ( (player = Player1) => positions /: player2_warships & card(player1_warships) < FLEET_SIZE) & 
        ( (player = Player2) => positions /: player1_warships & card(player2_warships) < FLEET_SIZE)

    THEN
        IF
            // Check overlap error if ships conflict
            {positions} /\ (player1_warships \/ player2_warships) /= {}
        THEN
            report := Error_Ships_Overlapped
        ELSE
            IF
                player = Player1 &
                card(player1_warships) /= FLEET_SIZE
            THEN
                // Add positions to Player1's warships
                player1_warships := player1_warships \/ {positions} ||
                report := Success_Ships_Deployed 
            ELSIF
                player = Player2 &
                card(player2_warships) /= FLEET_SIZE
            THEN
                // Add positions to Player2's warships
                player2_warships := player2_warships \/ {positions} ||
                report := Success_Ships_Deployed
            END
        END;
        IF
            card(player1_warships) = FLEET_SIZE &
            card(player2_warships) = FLEET_SIZE
        THEN
            // Set game status to Ongoing when both fleets are deployed
            current_game_status := Ongoing 
        END        
    END;
    
    // Operation to allow a player to shoot at a target grid square
    report <-- playerShoots (target) = 
    PRE
        current_game_status = Ongoing &
        target : GRID
    THEN
        IF
            current_player = Player1
        THEN
            IF
                // Check if the target square is in Player2's warships
                target : player2_warships
            THEN
                // Remove the target square from Player2's warships
                player2_warships := player2_warships - {target} ||
                report := Hit ||
                player1_hits := player1_hits \/ {target}
            ELSE
                report := Miss
            END || current_player := Player2
        ELSE 
            IF
                // Check if the target square is in Player1's warships
                target : player1_warships
            THEN
                // Remove the target square from Player1's warships
                player1_warships := player1_warships - {target} || 
                report := Hit || 
                player2_hits := player2_hits \/ {target}
            ELSE
                report := Miss
            END || current_player := Player1
        END;
        IF
            player1_warships = {}
        THEN
            // Player2 wins if Player1 has no ships left
            current_game_status := Player2_WON
        ELSIF
            player2_warships = {}
        THEN
            // Player1 wins if Player2 has no ships left
            current_game_status := Player1_WON
        END ||
        // Increment shot count for current player
        shots_taken := shots_taken <+ {current_player |-> shots_taken(current_player) + 1}
    END;
    
    // Operation to retrieve the locations of warships for a specific player
    shipSquares <-- shipLocations (player) =
    PRE
        player : PLAYERS
    THEN
        IF 
            player = Player1
        THEN
            shipSquares := player1_warships
        ELSE
            shipSquares := player2_warships
        END
    END;
    
    // Operation to return the number of ships left for both players
    shipCounts <-- shipsLeft =
    BEGIN
        shipCounts := {Player1 |-> card(player1_warships), Player2 |-> card(player2_warships)}
    END;
    
    // Operation to return the number of shots taken by a specific player
    shotCount <-- shotsTaken (player) = 
    PRE
        player : PLAYERS
    THEN
        shotCount := shots_taken(player) 
    END;
    
    // Operation to check the current game status
    report <-- gameStatus = 
    BEGIN
        report := current_game_status
    END

END