/*
 * Simple (quadrant-unaware) line drawing program.
 *
 * Currently draws a line (given a slope) to the console, with #-marks.
 * I wrote this one sleepless morning, and liked it.
 */

#define indexinto(bf, pt) get_buffr(bf)[as_common(bf)->how_wide*(pt).y+(pt).x]
#define as_common(BUFFER)  ((struct buf_dimension*)(BUFFER)         )
#define get_buffr(BUFFER) (((struct masked_buffer*)(BUFFER))->buffer)

#define add_slope(pt, ce) ((struct point) { (pt).x + (ce).lateral_growth,\
                                            (pt).y + (ce).upright_growth })

#define in_bounds(pt, bf) (((pt.x) < as_common(bf)->how_wide &\
                           ((pt.y) < as_common(bf)->how_high)))


#define square(x) ((x)*(x))
#define distances(pa, pb) (square((pa).x - (pb).x) + square((pa).y - (pb).y))

static inline unsigned min_of(const int* arr, unsigned len) {
	unsigned acc = 0;
	while (--len + 1) acc = (arr[acc] <= arr[len]) ? acc : len;

	return acc;
}

struct point { int x,y; };
struct line_coefficient {
	int upright_growth; /* "Rise" */
	int lateral_growth; /* "Run"  */
};

struct buf_dimension {
	unsigned how_high;
	unsigned how_wide;
};

struct  common_buffer        { struct buf_dimension dim; /* Subclass it. */ };
struct  masked_buffer        { struct buf_dimension dim; short buffer[   ]; };
#define static_b(X,Y) struct { struct common_buffer par; short buffer[X*Y]; }

void draw_line (struct common_buffer* graph, struct line_coefficient slope) {
	int y_delta = slope.upright_growth;
	int x_delta = slope.lateral_growth;

	static const struct            point zro = {0, 0};
	static const struct line_coefficient one = {1, 1};
	static const struct line_coefficient x_p = {1, 0};
	static const struct line_coefficient y_p = {0, 1};

	     struct point   anc = add_slope(zro, slope);
	for (struct point place = {0,0}; in_bounds(place, graph);) {

		const struct point C[] = /* Candidates for the next point to mark. */
		  {add_slope(place, one), add_slope(place, x_p), add_slope(place, y_p)};

		const   signed int D[] = /* Distances between candidates & anchor. */
		  {distances(C [0], anc), distances(C [1], anc), distances(C [2], anc)};

		indexinto(graph,place) = '#' - ' ';
		unsigned int min = min_of(D, sizeof(D)/sizeof(*D));
		if (!D[min]) anc = add_slope(anc, slope);
		           place = C[min];
	}
}

/*
 * Small program for using the above.
 */

#include <stdio.h>

void fmtbuffer (struct common_buffer* buffer, FILE* outs) {
	for (int y = 0; y < as_common(buffer)->how_high; ++y) {
	for (int x = 0; x < as_common(buffer)->how_wide; ++x) {
	     int d = as_common(buffer)->how_high - y - 1;
		fputc(get_buffr(buffer)[d*as_common(buffer)->how_wide + x] + ' ', outs);
	}   fputc('\n', outs); }
}

int main() {
	static_b(20, 20) buffer = {{20, 20}, {0}};
	draw_line(as_common(&buffer), (struct line_coefficient){1, 3});
	fmtbuffer(as_common(&buffer), stdout);
}
