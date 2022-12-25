select TeamId, count(*) as Solved
from (
	select distinct TeamId, ContestId, Letter
	from Runs natural join Sessions
	where Accepted = 1
) sub
group by TeamId