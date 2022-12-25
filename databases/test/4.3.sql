asdasdfasfaAAAAAAAAAAAA

select Letter
from Sessions natural join Runs
where
	ContestId = :ContestId
	and Accepted = 1
group by Letter
having count(*) =
