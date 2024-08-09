pragma circom 2.0.0;

include "circomlib/circuits/comparators.circom";
include "circomlib/circuits/sign.circom";
include "circomlib/circuits/bitify.circom"; // For Num2Bits component
include "circomlib/poseidon.circom"; // For Poseidon hashing

/*
Implements algorithms for working with geometric lines.
Designed to work over a subset of points of the field <= sqrt(p) that doesn't wrap around.
We assume that the caller implements its own range checks.
*/

/*
Returns 1 if two lines segments intersect, 0 otherwise.
*/
template Intersects(grid_bits) {
    signal input line1[2][2];
    signal input line2[2][2];
    signal output out;

    /*
    Make sure neither of the lines are degenerate single points
    */
    component eq[4];
    for (var i=0; i<2; i++) {
        eq[i] = IsEqual();
        eq[i].in[0] <== line1[0][i];
        eq[i].in[1] <== line1[1][i];

        eq[i+2] = IsEqual();
        eq[i+2].in[0] <== line1[0][i];
        eq[i+2].in[1] <== line1[1][i];
    }
    eq[0].out * eq[1].out === 0;
    eq[2].out * eq[3].out === 0;

    /*
    Setup orientation circuits:
        Orientation[0] takes inputs line1 and line2[0]
        Orientation[1] takes inputs line1 and line2[1]
        Orientation[2] takes inputs line2 and line2[0]
        Orientation[3] takes inputs line2 and line2[1]

    Similarly for inRect circuits
    */
    component orientation[4];
    component inRect[4];
    for (var i=0; i<2; i++) {
        // Orientation with respect to line1

        orientation[i] = Orientation(grid_bits);
        // line1 point 1
        orientation[i].points[0][0] <== line1[0][0];
        orientation[i].points[0][1] <== line1[0][1];
        // line1 point 2
        orientation[i].points[1][0] <== line1[1][0];
        orientation[i].points[1][1] <== line1[1][1];
        // line2 point i
        orientation[i].points[2][0] <== line2[i][0];
        orientation[i].points[2][1] <== line2[i][1];

        // Point on line 1
        inRect[i] = InRect(grid_bits);
        inRect[i].line[0][0] <== line1[0][0];
        inRect[i].line[0][1] <== line1[0][1];
        inRect[i].line[1][0] <== line1[1][0];
        inRect[i].line[1][1] <== line1[1][1];
        inRect[i].point[0] <== line2[i][0];
        inRect[i].point[1] <== line2[i][1];

        // Orientation with respect to line2
        orientation[i+2] = Orientation(grid_bits);
        // line2 point 1
        orientation[i+2].points[0][0] <== line2[0][0];
        orientation[i+2].points[0][1] <== line2[0][1];
        // line2 point 2
        orientation[i+2].points[1][0] <== line2[1][0];
        orientation[i+2].points[1][1] <== line2[1][1];
        // line1 point i
        orientation[i+2].points[2][0] <== line1[i][0];
        orientation[i+2].points[2][1] <== line1[i][1];

        // Point on line 2
        inRect[i+2] = InRect(grid_bits);
        inRect[i+2].line[0][0] <== line2[0][0];
        inRect[i+2].line[0][1] <== line2[0][1];
        inRect[i+2].line[1][0] <== line2[1][0];
        inRect[i+2].line[1][1] <== line2[1][1];
        inRect[i+2].point[0] <== line1[i][0];
        inRect[i+2].point[1] <== line1[i][1];
    }

    // If both points of each line segments are on different sides (i.e., have different orientations wrt) the other line, the
    // line segments certainly intersect.
    // This expression is 0 (false) if the orientations of both points of either line segments are equal.
    signal general_intersection <== (orientation[0].out - orientation[1].out) * (orientation[2].out - orientation[3].out);

    // Handle special case: if a point is collinear with the other line, and it lies on that line, then the line segments intersect
    // TODO: simplify by using an OnSegment component, which is equivalent to the below, but will require repeated computation of orientation.
    signal not_special_case[4];
    for (var i=0; i<4; i++) {
        not_special_case[i] <== orientation[i].out + 1 - inRect[i].out; // 0 if we're collinear and within the appropriate range
    }
    signal sc1 <== not_special_case[0] * not_special_case[1];
    signal sc2 <== not_special_case[2] * not_special_case[3];
    signal no_special_case <== sc1 * sc2;

    // Final result
    component not_general_intersection = IsZero();
    not_general_intersection.in <== general_intersection;
    signal not_out <== not_general_intersection.out * no_special_case;

    component negate = IsZero();
    negate.in <== not_out;
    out <== negate.out;
}

/*
Returns 1 if the 3 points are arranged in a clockwise order,
0 if they are in a line, and 2 if they are in a counter-clockwise order.

We use the slopes of the lines (p0, p1) and (p1, p02) to determine the orientation.
If the first slope is greater it's clockwise, if the second is greater it's anticlockwise,
and if they're equal it's in a line.

The slope of (p0, p1) is (y1 - y0) / (x1 - x0), and the slope of (p1,  p2) is (y2 - y1) / (x2 - x1).
Therefore the following expression will be positive for clockwise etc:
    f = (y1 - y0) / (x1 - x0) - (y2 - y1) / (x2 - x1)
      = (y1 - y0) * (x2 - x1) - (y2 - y1) * (x1 - x0)

Note that f is in the range (-(2^grid_bits)^2, (2^grid_bits)^2), so we have to make sure 2^grid_bits^2 < 2^252 (since 2^252 < p), or we overflow.
So grid_bits <= 127
*/
template Orientation(grid_bits) {
    signal input points[3][2];
    signal output out;

    assert(grid_bits <= 126);

    // (y1 - y0) * (x2 - x1) - (y2 - y1) * (x1 - x0)
    signal part <== (points[1][1] - points[0][1]) * (points[2][0] - points[1][0]);
    signal f <== part - (points[2][1] - points[1][1]) * (points[1][0] - points[0][0]);
    
    // Find the sign of f
    component num2Bits = Num2Bits(254);
    num2Bits.in <== f;

    component isNegative = Sign();
    for (var i=0; i<254; i++) {
        isNegative.in[i] <== num2Bits.out[i];
    }
    
    // Find out whether f is 0
    component isZero = IsZero();
    isZero.in <== f;
    signal nonZero <== 1-isZero.out;

    // Calculate the orientation
    // nonZero  | isNegative    | Orientation
    // 0        | 0             | 0
    // 0        | 1             | 0
    // 1        | 0             | 1
    // 1        | 1             | 2
    out <== nonZero*(isNegative.sign+1);

    // confirm that the output is of the correct form
    signal x <== out * (out - 1);
    x * (out - 2) === 0;
}

/*
Returns 1 if the point lies in a rectangle specified by its two corners, 0 otherwise
*/
template InRect(grid_bits) {
    signal input line[2][2];
    signal input point[2];
    signal output out;

    // order the x and y values
    component ordered_x = Order(grid_bits);
    ordered_x.in[0] <== line[0][0];
    ordered_x.in[1] <== line[1][0];

    component ordered_y = Order(grid_bits);
    ordered_y.in[0] <== line[0][1];
    ordered_y.in[1] <== line[1][1];

    // Check that the point is on the x-projection
    component aboveMinX = LessEqThan(grid_bits);
    aboveMinX.in[0] <== ordered_x.out[0];
    aboveMinX.in[1] <== point[0];

    component belowMaxX = LessEqThan(grid_bits);
    belowMaxX.in[0] <== point[0];
    belowMaxX.in[1] <== ordered_x.out[1];

    signal on_x_projection <== aboveMinX.out * belowMaxX.out;

    // Check that the point is on the y-projection
    component aboveMinY = LessEqThan(grid_bits);
    aboveMinY.in[0] <== ordered_y.out[0];
    aboveMinY.in[1] <== point[1];

    component belowMaxY = LessEqThan(grid_bits);
    belowMaxY.in[0] <== point[1];
    belowMaxY.in[1] <== ordered_y.out[1];

    signal on_y_projection <== aboveMinY.out * belowMaxY.out;

    // return whether the point is on both the x and y projections
    out <== on_x_projection * on_y_projection;

    // make sure the output is 0 or 1
    out * (out - 1) === 0;
}

// From https://docs.circom.io/more-circuits/more-basic-circuits/#extending-our-multiplier-to-n-inputs
template MultiplierN (N){
   //Declaration of signals.
   signal input in[N];
   signal output out;
   component comp[N-1];

   //Statements.
   for(var i = 0; i < N-1; i++){
       comp[i] = Multiplier2();
   }
   comp[0].in1 <== in[0];
   comp[0].in2 <== in[1];
   for(var i = 0; i < N-2; i++){
       comp[i+1].in1 <== comp[i].out;
       comp[i+1].in2 <== in[i+2];

   }
   out <== comp[N-2].out; 
}

// Multiplies 2 numbers (from circom docs)
template Multiplier2() {
    signal input in1;
    signal input in2;
    signal output out;
    out <== in1*in2;
}

/*
Compare a signal to some constant
Aids readability by handling binary decomposition of the signal
*/
template Comp(ct) {
    signal input in;
    signal output out;

    // TODO: optimise by using grid_bits instead of 254
    component num2Bits = Num2Bits(254);
    num2Bits.in <== in;

    component compare = CompConstant(ct);
    for (var i=0; i<254; i++) {
        compare.in[i] <== num2Bits.out[i];
    }

    out <== compare.out;
}

/*
Return two values in order
*/
template Order(grid_bits) {
    signal input in[2];
    signal output out[2];

    component lt = GreaterThan(grid_bits);
    lt.in[0] <== in[0];
    lt.in[1] <== in[1];

    out[0] <== (in[1] - in[0])*lt.out + in[0];
    out[1] <== (in[0] - in[1])*lt.out + in[1];
}

// RayTracing template to check if a point is inside a polygon
template RayTracing(n, grid_bits) {
    signal input point[2];            // Input point (x, y) to check
    signal input polygon[n][2];       // Polygon coordinates
    signal output out;                // Output 1 if inside, 0 if outside

    // Make sure the point is in the range (0, 2^grid_bits)
    component comp[2];
    for (var i=0; i<2; i++) {
        comp[i] = Comp(2**grid_bits-1);
        comp[i].in <== point[i];
        comp[i].out === 0;
    }

    // We consider all points that share a y coordinate with a vertex to be outside the polygon
    // This avoids edge cases where the ray intersects the polygon at a corner
    component mult = MultiplierN(n);
    for (var i=0; i<n; i++) {
        mult.in[i] <== polygon[i][1] - point[1];
    }

    // Normalize to 0 or 1
    component isZero = IsZero();
    isZero.in <== mult.out;
    signal not_on_vertex_line <== 1-isZero.out;

    // Count the number of intersections with the ray
    component intersections[n];
    var intersection_sum = 0;
    for (var i=0; i<n; i++) {
        intersections[i] = Intersects(grid_bits);
        // line1 is the ray, from (0,y) to (x,y)
        intersections[i].line1[0][0] <== 0;
        intersections[i].line1[0][1] <== point[1];
        intersections[i].line1[1][0] <== point[0];
        intersections[i].line1[1][1] <== point[1];

        // line2 is the edge from polygon[n] to polygon[(n+1)%n]
        intersections[i].line2[0][0] <== polygon[i][0];
        intersections[i].line2[0][1] <== polygon[i][1];
        intersections[i].line2[1][0] <== polygon[(i+1)%n][0];
        intersections[i].line2[1][1] <== polygon[(i+1)%n][1];

        // Make sure the value is 0 or 1
        intersections[i].out * (intersections[i].out - 1) === 0;
        intersection_sum += intersections[i].out;
    }

    signal intersection_count <== intersection_sum;
    component num2Bits = Num2Bits(n+1); // n+1 bits is easily sufficient to hold a value up to n
    num2Bits.in <== intersection_count;
    signal odd_intersections <== num2Bits.out[0];
    out <== odd_intersections * not_on_vertex_line;
}

// HashCoordinate template to hash a coordinate using Poseidon
template HashCoordinate() {
    signal input x;
    signal input y;
    signal output coordHash;

    // Use an array of size 2 to pass x and y as inputs to Poseidon
    signal inputs[2];
    inputs[0] <== x;
    inputs[1] <== y;

    // Pass the inputs array to the Poseidon hash function
    component poseidonHash = Poseidon(2);
    poseidonHash.inputs[0] <== inputs[0];
    poseidonHash.inputs[1] <== inputs[1];

    // Get the output hash
    coordHash <== poseidonHash.out;
}

// HashPolygon template to hash all the coordinates of a polygon
template HashPolygon(n) {
    signal input coords[2*n];        // Input coordinates for the polygon (2*n signals for x and y of n points)
    signal output polygonHash;       // Output hash of the polygon

    // Fixed-size array for storing coordinate hashes
    signal coordHashes[n];

    // Hash each coordinate and store the hash in coordHashes array
    component hashers[n];
    for (var i = 0; i < n; i++) {
        hashers[i] = HashCoordinate();
        hashers[i].x <== coords[2*i];
        hashers[i].y <== coords[2*i+1];
        coordHashes[i] <== hashers[i].coordHash;
    }

    // Instantiate the Poseidon hash function to hash the entire array of coordinate hashes
    component poseidonHash = Poseidon(n);
    for (var i = 0; i < n; i++) {
        poseidonHash.inputs[i] <== coordHashes[i];
    }

    // Get the final polygon hash
    polygonHash <== poseidonHash.out;
}

// VerifyMerkleProof template to verify a Merkle proof
template VerifyMerkleProof(depth) {
    signal input leaf;
    signal input root;
    signal input pathIndices[depth];
    signal input pathElements[depth];
    signal output isValid;

    signal currentHash[depth + 1];
    signal input0[depth];
    signal input1[depth];

    // Declare intermediate signals for the loop
    signal pathIsOne_input0[depth];
    signal pathIsZero_input0[depth];
    signal pathIsOne_input1[depth];
    signal pathIsZero_input1[depth];

    // Initialize the first hash
    currentHash[0] <== leaf;

    // Declare Poseidon components outside the loop
    component poseidonHash[depth];

    // Loop to compute the hash at each depth level of the Merkle proof
    for (var i = 0; i < depth; i++) {
        poseidonHash[i] = Poseidon(2); // Poseidon with 2 inputs

        // Calculate the input0 signals
        pathIsOne_input0[i] <== pathIndices[i] * pathElements[i];
        pathIsZero_input0[i] <== (1 - pathIndices[i]) * currentHash[i];
        input0[i] <== pathIsOne_input0[i] + pathIsZero_input0[i];

        // Calculate the input1 signals
        pathIsOne_input1[i] <== pathIndices[i] * currentHash[i];
        pathIsZero_input1[i] <== (1 - pathIndices[i]) * pathElements[i];
        input1[i] <== pathIsOne_input1[i] + pathIsZero_input1[i];

        // Assign the inputs to the Poseidon hash function
        poseidonHash[i].inputs[0] <== input0[i];
        poseidonHash[i].inputs[1] <== input1[i];

        // Update the current hash
        currentHash[i + 1] <== poseidonHash[i].out;
    }

    // Introduce the difference signal
    signal diff;

    signal output flag2;

    flag2 <== currentHash[depth];
    diff <== currentHash[depth] - root;

    // Enforce that diff is zero if and only if currentHash[depth] equals root
    isValid <== 1 - (diff * diff);
}

// ValidateCoordinateInclusion template to check if a coordinate is inside the polygon
// and to verify the polygon's hash and Merkle proof
template ValidateCoordinateInclusion(depth, n, grid_bits) {
    signal input px;                  // The x-coordinate of the point to check
    signal input py;                  // The y-coordinate of the point to check
    signal input polygonHash;         // The hash of the entire polygon
    signal input polygon[n][2];       // The coordinates of the polygon
    signal input root;                // The Merkle root
    signal input pathIndices[depth];  // The Merkle proof path indices
    signal input pathElements[depth]; // The Merkle proof path elements
    signal output isValid;            // The output signal indicating if the point is valid

    signal output flag1;
    signal output flag2;

    // Use RayTracing to check if the point is inside the polygon
    component rayTracing = RayTracing(n, grid_bits);
    rayTracing.point[0] <== px;
    rayTracing.point[1] <== py;
    for (var i = 0; i < n; i++) {
        rayTracing.polygon[i][0] <== polygon[i][0];
        rayTracing.polygon[i][1] <== polygon[i][1];
    }

    // Hash the polygon
    component hashPolygon = HashPolygon(n);
    for (var i = 0; i < n; i++) {
        hashPolygon.coords[2*i] <== polygon[i][0];
        hashPolygon.coords[2*i+1] <== polygon[i][1];
    }

    // Verify Merkle proof
    component verifyMerkleProof = VerifyMerkleProof(depth);
    verifyMerkleProof.leaf <== hashPolygon.polygonHash;
    verifyMerkleProof.root <== root;
    for (var i = 0; i < depth; i++) {
        verifyMerkleProof.pathIndices[i] <== pathIndices[i];
        verifyMerkleProof.pathElements[i] <== pathElements[i];
    }

    flag1 <== verifyMerkleProof.isValid; //❌
    flag2 <== verifyMerkleProof.flag2;

    // Introduce an intermediate signal for the equality check
    signal polygonHashDiff;
    polygonHashDiff <== hashPolygon.polygonHash - polygonHash;

    // Create a signal to enforce the equality (polygonHashDiff should be 0)
    signal polygonHashIsEqual;
    polygonHashIsEqual <== 1 - (polygonHashDiff * polygonHashDiff);

    // Combine all conditions in a quadratic way
    signal combinedValidity;
    signal combinedValidity1;
    combinedValidity1 <== rayTracing.out * polygonHashIsEqual;
    combinedValidity <== combinedValidity1 * verifyMerkleProof.isValid;

    // Assign to the final output signal
    isValid <== combinedValidity;
}

component main = ValidateCoordinateInclusion(16, 4, 32);

/* INPUT = {
  "px": "99930794",
  "py": "95850986",
  "polygonHash": "19734256724370939262826947009735877839971681289001157384192434648867876200933",
  "polygon": [
    ["99930607", "95850886"],
    ["99930856", "95851062"],
    ["99930840", "95850853"],
    ["99930610", "95851072"]
  ],
  "root": "2703440162454052840609636720528243608663031709412357648362337729401815863073",
  "pathIndices": [
    "0", "1", "0", "1", "0", "1", "0", "1",
    "0", "1", "0", "1", "0", "1", "0", "1"
  ],
  "pathElements": [
    "19734256724370939262826947009735877839971681289001157384192434648867876200933",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "3333333333333333333333333333333333333333333333333333333333333333",
    "4444444444444444444444444444444444444444444444444444444444444444",
    "5555555555555555555555555555555555555555555555555555555555555555",
    "6666666666666666666666666666666666666666666666666666666666666666",
    "7777777777777777777777777777777777777777777777777777777777777777",
    "8888888888888888888888888888888888888888888888888888888888888888",
    "9999999999999999999999999999999999999999999999999999999999999999",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "2222222222222222222222222222222222222222222222222222222222222222",
    "0000000000000000000000000000000000000000000000000000000000000000"
  ]
} */