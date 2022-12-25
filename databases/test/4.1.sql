select SessionId, count(distinct Letter) as Solved
from Runs
where Accepted = 1
group by SessionId