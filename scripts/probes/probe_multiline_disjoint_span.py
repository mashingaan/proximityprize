"""Full F17 transverse-plane census in the existing disjoint two-pencil span."""
import itertools
import json


def main():
    p = 17
    first = [(-1,-2,-3,0,0,0),(1,1,1,0,0,0)]
    second = [(0,0,0,4,5,6),(0,0,0,-1,-1,-1)]
    histogram = {}
    other_maximum = 0
    three_point_planes = []
    for a,b,c,d in itertools.product(range(p),repeat=4):
        # The quotient image is the identity on both bases.
        row0 = [(a*x+b*y+(1-a)*z-b*w) % p
                for x,y,z,w in zip(*first,*second)]
        row1 = [(c*x+d*y-c*z+(1-d)*w) % p
                for x,y,z,w in zip(*first,*second)]
        support_size = sum(x != 0 or y != 0 for x,y in zip(row0,row1))
        assert support_size > 2
        low = [gamma for gamma in range(p)
               if sum((x+gamma*y) % p != 0 for x,y in zip(row0,row1)) <= 2]
        count = len(low)+int(sum(y != 0 for y in row1) <= 2)
        histogram[count] = histogram.get(count,0)+1
        original = (a,b,c,d) in ((0,0,0,0),(1,0,0,1))
        if original:
            assert count == 3
        else:
            other_maximum = max(other_maximum,count)
            assert count <= 2
        if count >= 3:
            three_point_planes.append(dict(matrix=[a,b,c,d],affine_scalars=low))
    assert sum(histogram.values()) == p**4
    assert len(three_point_planes) == 2
    print(json.dumps(dict(field=p,original_length=8,code_distance=5,error_budget=2,
                         transverse_planes_checked=p**4,
                         projective_low_weight_histogram=histogram,
                         original_three_point_planes=three_point_planes,
                         maximum_other_plane_low_weight_points=other_maximum,
                         scope='all transverse planes in the sum of the two disjoint error pencils',
                         evidence='exact enumeration including the projective infinity point',
                         universal_proof='handwritten disjoint-support rank decomposition',
                         new_lean_theorem=False,threshold_improvement=False),indent=2))


if __name__ == '__main__':
    main()
